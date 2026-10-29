package com.botwrecompandroid;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.function.LongConsumer;

import javax.crypto.Cipher;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;

// The game's files (exefs/ and romfs/) taken straight out of the player's own Breath of the Wild base package - a
// cartridge image (.xci) or an eShop package (.nsp) - with the player's own console keys (prod.keys), the way hactool
// does it: the base program NCA is found, its header decrypted (AES-XTS, the header key), its section key unwrapped
// (the key area with key_area_key_application_XX, or the ticket's title key with titlekek_XX), and its two sections -
// exefs (PFS0) and romfs (IVFC) - decrypted (AES-CTR) and read out file by file. Only the BASE game (1.0.0) is
// handled: an update's program NCA (BKTR sections) is skipped, so 1.6.0 / 1.8.2 still need extracted folders.
// Ported from LAS Recomp for Android's NxPackage (LASRecomp-Android-Plus, MIT); changes: the title id, no dependency
// on the activity, an API that streams single files (the romfs is never written out as a folder), thread-safe reads.
// Plain Java (no Android classes): `java NxPackage.java <package> <prod.keys> <dest|->` runs it on a computer or in Termux.
final class NxPackage {
    static final long TITLE_ID = 0x01007EF00011E000L;  // The Legend of Zelda: Breath of the Wild (base game)

    interface Progress { void at(long done, long total); }

    static final class KeyMissing extends Exception { KeyMissing(String k) { super(k); } }
    static final class Corrupt extends Exception { Corrupt(String w) { super(w); } }

    // A file inside the package's exefs or romfs: path (exefs: its name; romfs: relative, no leading slash)
    static final class RomFile {
        final String path;
        final long off, size;  // in its section
        final boolean inExefs;
        RomFile(String path, long off, long size, boolean inExefs) {
            this.path = path; this.off = off; this.size = size; this.inExefs = inExefs;
        }
    }

    // A reason for the player, from what open() / the reads threw
    static String explain(Throwable e) {
        if (e instanceof KeyMissing) {
            String m = e.getMessage();
            if (m.startsWith("title key")) return "The package has no ticket (.tik) for this game, so it can't be decrypted. Use a full eShop .nsp dump.";
            if (m.equals("badkeys")) return "The keys can't decrypt this package - prod.keys is from another console, or damaged.";
            return "prod.keys has no \"" + m + "\" - it is probably from an older firmware than this game needs. Dump a newer prod.keys.";
        }
        if (e instanceof Corrupt) {
            String m = e.getMessage();
            if (m.equals("compressed")) return "Compressed packages (.nsz / .xcz) can't be used. Decompress it to .nsp / .xci first.";
            if (m.equals("notgame")) return "No Breath of the Wild base game found in this package.";
            if (m.equals("updateonly")) return "This package is only an update. Pick the base game's .nsp / .xci (the setup uses v1.0.0).";
            return "The package looks damaged or unsupported (" + m + ").";
        }
        return e.getClass().getSimpleName() + (e.getMessage() != null ? ": " + e.getMessage() : "");
    }

    // prod.keys / title.keys: "name = hex" lines
    static Map<String, byte[]> parseKeys(InputStream in) throws IOException {
        Map<String, byte[]> out = new HashMap<>();
        BufferedReader r = new BufferedReader(new InputStreamReader(in, StandardCharsets.US_ASCII));
        for (String line; (line = r.readLine()) != null; ) {
            int eq = line.indexOf('=');
            if (eq < 0) continue;
            String name = line.substring(0, eq).trim().toLowerCase(Locale.ROOT), hex = line.substring(eq + 1).trim();
            if (name.isEmpty() || hex.isEmpty() || (hex.length() & 1) != 0) continue;
            byte[] b = new byte[hex.length() / 2];
            boolean ok = true;
            for (int i = 0; i < b.length && ok; i++) {
                int hi = Character.digit(hex.charAt(2 * i), 16), lo = Character.digit(hex.charAt(2 * i + 1), 16);
                ok = hi >= 0 && lo >= 0;
                b[i] = (byte) (hi << 4 | lo);
            }
            if (ok) out.put(name, b);
        }
        return out;
    }

    private final FileChannel pkg;
    private final Map<String, byte[]> keys;
    private final List<Entry> ncas = new ArrayList<>(), tickets = new ArrayList<>();
    private boolean compressed;
    private List<RomFile> exefsFiles, romfsFiles;

    private static final class Entry {
        final String name;
        final long off, size;
        Entry(String name, long off, long size) { this.name = name; this.off = off; this.size = size; }
    }

    NxPackage(FileChannel pkg, Map<String, byte[]> keys) { this.pkg = pkg; this.keys = keys; }

    // Finds the base program, decrypts its keys and reads the exefs and romfs file tables. Throws KeyMissing / Corrupt
    // (explain() words them) or an IOException.
    void open() throws Exception {
        listPackage();
        openProgram();
        exefsFiles = readExefsTable();
        romfsFiles = readRomfsTable();
    }

    List<RomFile> exefsFiles() { return exefsFiles; }
    List<RomFile> romfsFiles() { return romfsFiles; }

    // exefs/main's first 0x48 bytes (the start the app reads its version from)
    byte[] mainHead() throws Exception {
        for (RomFile f : exefsFiles)
            if (f.path.equals("main") && f.size >= 0x48) return readFile(f, 0x48);
        throw new Corrupt("exefs/main");
    }

    // the first max bytes of a file
    byte[] readFile(RomFile f, int max) throws Exception {
        int n = (int) Math.min(f.size, max);
        byte[] b = new byte[n];
        (f.inExefs ? exefs : romfs).read(f.off, b, 0, n);
        return b;
    }

    // a file written whole to out (a .part first, then renamed); onBytes gets the bytes as they go. Safe to call from
    // several threads at once, for different files.
    void write(RomFile f, File out, LongConsumer onBytes) throws Exception {
        File dir = out.getParentFile();
        if (dir != null && !dir.isDirectory() && !dir.mkdirs() && !dir.isDirectory()) throw new IOException("mkdir " + dir);
        File part = new File(out.getPath() + ".part");
        Section s = f.inExefs ? exefs : romfs;
        byte[] buf = new byte[(int) Math.max(16, Math.min(4 << 20, f.size))];
        try (FileOutputStream os = new FileOutputStream(part)) {
            for (long p = 0; p < f.size; ) {
                int n = (int) Math.min(buf.length, f.size - p);
                s.read(f.off + p, buf, 0, n);
                os.write(buf, 0, n);
                p += n;
                if (onBytes != null) onBytes.accept(n);
            }
        }
        if (out.exists() && !out.delete()) throw new IOException("replace " + out);
        if (!part.renameTo(out)) throw new IOException("rename " + out);
    }

    // ---- reading the package

    private ByteBuffer read(long off, int len) throws IOException, Corrupt {
        ByteBuffer b = ByteBuffer.allocate(len).order(ByteOrder.LITTLE_ENDIAN);
        while (b.hasRemaining()) {
            int n = pkg.read(b, off + b.position());
            if (n < 0) throw new Corrupt("short read at " + off);
        }
        b.flip();
        return b;
    }

    // a PFS0 (.nsp) or HFS0 (an .xci's partitions) file table at off: its files' (name, offset, size)
    private List<Entry> fileTable(long off, long limit) throws IOException, Corrupt {
        ByteBuffer h = read(off, 16);
        int magic = h.getInt(0), n = h.getInt(4), strSize = h.getInt(8);
        boolean hfs = magic == 0x30534648;  // "HFS0"
        if (!hfs && magic != 0x30534650) throw new Corrupt("no file table");  // "PFS0"
        int es = hfs ? 0x40 : 0x18;
        if (n < 0 || n > 10000 || strSize < 0 || strSize > (1 << 20)) throw new Corrupt("file table");
        ByteBuffer t = read(off + 16, n * es + strSize);
        long data = off + 16 + (long) n * es + strSize;
        List<Entry> out = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            long o = t.getLong(i * es), s = t.getLong(i * es + 8);
            int so = t.getInt(i * es + 16), e = n * es + so;
            if (so < 0 || so >= strSize) throw new Corrupt("file name");
            while (e < t.limit() && t.get(e) != 0) e++;
            String name = new String(t.array(), n * es + so, e - n * es - so, StandardCharsets.UTF_8);
            if (o < 0 || s < 0 || (limit > 0 && o + s > limit)) throw new Corrupt("file " + name);
            out.add(new Entry(name, data + o, s));
        }
        return out;
    }

    private void listPackage() throws IOException, Corrupt {
        long base = -1;
        for (long b : new long[] {0, 0x1000})  // (a cartridge dump with its key area in front: 0x1000 more)
            if (pkg.size() > b + 0x200 && read(b + 0x100, 4).getInt(0) == 0x44414548) { base = b; break; }  // "HEAD"
        List<Entry> files;
        if (base >= 0) {
            ByteBuffer h = read(base + 0x130, 8);
            List<Entry> parts = fileTable(base + h.getLong(0), 0);
            files = new ArrayList<>();
            for (Entry p : parts)  // (the game is in "secure"; "update" holds a system update, never wanted)
                if (p.name.equals("secure")) files.addAll(fileTable(p.off, p.size));
        } else {
            files = fileTable(0, 0);
        }
        for (Entry e : files) {
            String low = e.name.toLowerCase(Locale.ROOT);
            if (low.endsWith(".nca")) ncas.add(e);
            else if (low.endsWith(".tik")) tickets.add(e);
            else if (low.endsWith(".ncz")) compressed = true;
        }
        if (ncas.isEmpty()) throw new Corrupt(compressed ? "compressed" : "no NCA");
    }

    // ---- keys

    private byte[] key(String name) throws KeyMissing {
        byte[] k = keys.get(name);
        if (k == null) throw new KeyMissing(name);
        return k;
    }

    private static byte[] ecb(byte[] key, byte[] data, boolean decrypt) throws Exception {
        Cipher c = Cipher.getInstance("AES/ECB/NoPadding");
        c.init(decrypt ? Cipher.DECRYPT_MODE : Cipher.ENCRYPT_MODE, new SecretKeySpec(key, 0, 16, "AES"));
        return c.doFinal(data);
    }

    // a key of the master key generation rev: from prod.keys, or made from master_key_XX like hactool does
    private byte[] genKey(String name, int rev, boolean kek) throws Exception {
        String n = String.format(Locale.ROOT, "%s_%02x", name, rev);
        if (keys.containsKey(n)) return keys.get(n);
        byte[] mk = keys.get(String.format(Locale.ROOT, "master_key_%02x", rev));
        if (mk == null) throw new KeyMissing(n);
        if (!kek) return ecb(mk, key(name + "_source"), true);  // (titlekek)
        byte[] k = ecb(mk, key("aes_kek_generation_source"), true);
        k = ecb(k, key(name + "_source"), true);
        return ecb(k, key("aes_key_generation_source"), true);
    }

    // ---- the NCA header (0xC00 bytes, AES-XTS with Nintendo's big-endian sector tweak, 0x200-byte sectors)

    private byte[] ncaHeader(Entry e) throws Exception {
        byte[] hk = key("header_key");
        if (hk.length != 32) throw new KeyMissing("header_key");
        byte[] enc = read(e.off, 0xC00).array();
        Cipher k1 = Cipher.getInstance("AES/ECB/NoPadding"), k2 = Cipher.getInstance("AES/ECB/NoPadding");
        k1.init(Cipher.DECRYPT_MODE, new SecretKeySpec(hk, 0, 16, "AES"));
        k2.init(Cipher.ENCRYPT_MODE, new SecretKeySpec(hk, 16, 16, "AES"));
        byte[] out = new byte[enc.length], t = new byte[16], blk = new byte[16];
        for (int s = 0; s < enc.length / 0x200; s++) {
            byte[] tw = new byte[16];
            for (int i = 0; i < 8; i++) tw[15 - i] = (byte) ((long) s >>> (8 * i));
            k2.doFinal(tw, 0, 16, t, 0);
            for (int b = 0; b < 0x200; b += 16) {
                int o = s * 0x200 + b;
                for (int i = 0; i < 16; i++) blk[i] = (byte) (enc[o + i] ^ t[i]);
                k1.doFinal(blk, 0, 16, blk, 0);
                for (int i = 0; i < 16; i++) out[o + i] = (byte) (blk[i] ^ t[i]);
                int carry = 0;  // t *= x in GF(2^128), little-endian
                for (int i = 0; i < 16; i++) {
                    int v = (t[i] & 0xff) << 1 | carry;
                    carry = v >>> 8;
                    t[i] = (byte) v;
                }
                if (carry != 0) t[0] ^= (byte) 0x87;
            }
        }
        return out;
    }

    // ---- a section of the program NCA, decrypted (AES-CTR)

    private final class Section {
        final long start, size;  // in the package
        final long inNca;        // where it starts in its NCA (the counter counts from the NCA's start)
        final byte[] key, ctrHigh;
        final ByteBuffer fsh;    // its FS header (0x200)
        Section(long start, long inNca, long size, byte[] key, ByteBuffer fsh) {
            this.start = start; this.inNca = inNca; this.size = size; this.key = key; this.fsh = fsh;
            ctrHigh = new byte[8];
            for (int i = 0; i < 8; i++) ctrHigh[i] = fsh.get(0x140 + 7 - i);
        }
        // len bytes at off (section-relative) into out[at..]; a cipher per call: several threads may read at once
        void read(long off, byte[] out, int at, int len) throws Exception {
            if (len == 0) return;
            if (off < 0 || off + len > size) throw new Corrupt("section range");
            long a = off & ~15L;
            int skip = (int) (off - a), n = (len + skip + 15) & ~15;
            ByteBuffer raw = NxPackage.this.read(start + a, n);
            byte[] iv = new byte[16];
            System.arraycopy(ctrHigh, 0, iv, 0, 8);
            long blk = (inNca + a) >>> 4;
            for (int i = 0; i < 8; i++) iv[15 - i] = (byte) (blk >>> (8 * i));
            Cipher c = Cipher.getInstance("AES/CTR/NoPadding");
            c.init(Cipher.DECRYPT_MODE, new SecretKeySpec(key, "AES"), new IvParameterSpec(iv));
            byte[] dec = c.doFinal(raw.array(), 0, n);
            System.arraycopy(dec, skip, out, at, len);
        }
        ByteBuffer read(long off, int len) throws Exception {
            byte[] b = new byte[len];
            read(off, b, 0, len);
            return ByteBuffer.wrap(b).order(ByteOrder.LITTLE_ENDIAN);
        }
    }

    private Section exefs, romfs;
    private long romfsBase;  // the RomFS inside its section (the IVFC's last level)

    // The game's base program: a package may also carry an update (a cartridge with its day-one patch, or an eShop
    // bundle): its program NCA has the same title id but patch sections (BKTR, encryption type 4) over the base's
    // RomFS and the update's exefs - never wanted here. The largest base program wins.
    private void openProgram() throws Exception {
        boolean anyHeader = false, anyPatch = false;
        List<Entry> cands = new ArrayList<>();
        List<byte[]> heads = new ArrayList<>();
        for (Entry e : ncas) {
            byte[] hb = ncaHeader(e);
            ByteBuffer h = ByteBuffer.wrap(hb).order(ByteOrder.LITTLE_ENDIAN);
            if (h.getInt(0x200) != 0x3341434E) continue;  // "NCA3" (anything else: wrong header key, or an old format)
            anyHeader = true;
            long id = h.getLong(0x210);  // (the update's program NCA may carry the update's title id, ...E800)
            if (h.get(0x205) != 0 || (id != TITLE_ID && id != TITLE_ID + 0x800)) continue;  // (content type 0: program)
            boolean patch = false;
            for (int s = 0; s < 4; s++) patch |= h.getInt(0x244 + s * 16) != 0 && hb[0x400 + s * 0x200 + 4] == 4;
            anyPatch |= patch;
            if (patch || id != TITLE_ID) continue;
            int at = 0;
            while (at < cands.size() && cands.get(at).size >= e.size) at++;
            cands.add(at, e);
            heads.add(at, hb);
        }
        if (cands.isEmpty()) throw anyPatch ? new Corrupt("updateonly") : anyHeader ? new Corrupt("notgame") : new KeyMissing("badkeys");
        Entry e = cands.get(0);
        byte[] hb = heads.get(0);
        ByteBuffer h = ByteBuffer.wrap(hb).order(ByteOrder.LITTLE_ENDIAN);
        int gen = Math.max(h.get(0x206) & 0xff, h.get(0x220) & 0xff), rev = gen > 0 ? gen - 1 : 0;
        boolean rights = false;
        for (int i = 0; i < 16; i++) rights |= h.get(0x230 + i) != 0;
        byte[] ctrKey;
        if (rights) {  // (an eShop package: the title key from its ticket)
            StringBuilder rid = new StringBuilder();
            for (int i = 0; i < 16; i++) rid.append(String.format(Locale.ROOT, "%02x", h.get(0x230 + i) & 0xff));
            byte[] tk = null;
            for (Entry t : tickets)
                if (t.name.toLowerCase(Locale.ROOT).startsWith(rid.toString()) && t.size >= 0x190) tk = read(t.off + 0x180, 16).array();
            if (tk == null) tk = keys.get(rid.toString());  // (title.keys lines, if the player put them in too)
            if (tk == null) throw new KeyMissing("title key " + rid);
            ctrKey = ecb(genKey("titlekek", rev, false), tk, true);
        } else {
            int idx = h.get(0x207) & 0xff;
            String[] kak = {"key_area_key_application", "key_area_key_ocean", "key_area_key_system"};
            if (idx > 2) throw new Corrupt("key area index");
            byte[] area = new byte[16];
            System.arraycopy(hb, 0x300 + 2 * 16, area, 0, 16);
            ctrKey = ecb(genKey(kak[idx], rev, true), area, true);
        }
        for (int s = 0; s < 4; s++) {  // (exefs: the first PFS0 - the logo's comes after it; romfs)
            long st = (h.getInt(0x240 + s * 16) & 0xffffffffL) * 0x200, en = (h.getInt(0x244 + s * 16) & 0xffffffffL) * 0x200;
            if (st == 0 && en == 0) continue;
            if (en <= st || en > e.size) throw new Corrupt("section " + s);
            ByteBuffer fsh = ByteBuffer.wrap(hb, 0x400 + s * 0x200, 0x200).slice().order(ByteOrder.LITTLE_ENDIAN);
            int type = fsh.get(2);  // (0 RomFS, 1 PFS0)
            if ((type == 1 && exefs != null) || (type == 0 && romfs != null) || type > 1) continue;
            if (fsh.get(4) != 3) throw new Corrupt("section " + s + " encryption " + fsh.get(4));  // (3: AES-CTR)
            Section sec = new Section(e.off + st, st, en - st, ctrKey, fsh);
            if (type == 1) exefs = sec;
            else romfs = sec;
        }
        if (exefs == null || romfs == null) throw new Corrupt("sections");
        // IVFC at 0x8 of the FS header: magic, id, master hash size, levels, then 6 x {offset, size, block, -}
        if (romfs.fsh.getInt(8) != 0x43465649) throw new Corrupt("IVFC");  // "IVFC"
        romfsBase = romfs.fsh.getLong(8 + 0x10 + 5 * 0x18);
    }

    // ---- the file tables

    private static String name(ByteBuffer b, int at, int len) {
        return new String(b.array(), b.arrayOffset() + at, len, StandardCharsets.UTF_8);
    }

    // exefs: a PFS0 at the hash info's data region (HierarchicalSha256: 0x8 + 0x38)
    private List<RomFile> readExefsTable() throws Exception {
        long pfs = exefs.fsh.getLong(8 + 0x38);
        ByteBuffer ph = exefs.read(pfs, 16);
        if (ph.getInt(0) != 0x30534650) throw new Corrupt("exefs");
        int n = ph.getInt(4), strSize = ph.getInt(8);
        if (n <= 0 || n > 64 || strSize < 0 || strSize > 4096) throw new Corrupt("exefs table");
        ByteBuffer t = exefs.read(pfs + 16, n * 0x18 + strSize);
        long dataAt = pfs + 16 + n * 0x18L + strSize;
        List<RomFile> ex = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            int so = t.getInt(i * 0x18 + 16), e = n * 0x18 + so;
            while (e < t.limit() && t.get(e) != 0) e++;
            String nm = name(t, n * 0x18 + so, e - n * 0x18 - so);
            if (nm.isEmpty() || nm.contains("/") || nm.startsWith(".")) throw new Corrupt("exefs name");
            ex.add(new RomFile(nm, dataAt + t.getLong(i * 0x18), t.getLong(i * 0x18 + 8), true));
        }
        boolean hasMain = false;
        for (RomFile f : ex) hasMain |= f.path.equals("main") && f.size >= 0x48;
        if (!hasMain) throw new Corrupt("exefs/main");
        return ex;
    }

    // the RomFS's directory tree: every file with its path, data offset and size
    private List<RomFile> readRomfsTable() throws Exception {
        ByteBuffer h = romfs.read(romfsBase, 0x50);
        if (h.getLong(0) != 0x50) throw new Corrupt("RomFS header");
        long dirOff = h.getLong(0x18), dirSize = h.getLong(0x20), fileOff = h.getLong(0x38), fileSize = h.getLong(0x40);
        long data = h.getLong(0x48);
        if (dirSize > (64 << 20) || fileSize > (64 << 20)) throw new Corrupt("RomFS tables");
        ByteBuffer dirs = romfs.read(romfsBase + dirOff, (int) dirSize), files = romfs.read(romfsBase + fileOff, (int) fileSize);
        List<RomFile> out = new ArrayList<>();
        walk(dirs, files, 0, "", data, out, 0);
        return out;
    }

    private void walk(ByteBuffer dirs, ByteBuffer files, int d, String path, long data, List<RomFile> out, int depth) throws Corrupt {
        if (depth > 64 || d < 0 || d + 0x18 > dirs.limit()) throw new Corrupt("RomFS directory");
        for (int f = dirs.getInt(d + 12); f != -1; ) {
            if (f < 0 || f + 0x20 > files.limit()) throw new Corrupt("RomFS file");
            int nl = files.getInt(f + 0x1C);
            String n = name(files, f + 0x20, nl);
            if (n.isEmpty() || n.equals(".") || n.equals("..") || n.contains("/")) throw new Corrupt("RomFS name");
            out.add(new RomFile(path.isEmpty() ? n : path + "/" + n, romfsBase + data + files.getLong(f + 8), files.getLong(f + 16), false));
            f = files.getInt(f + 4);
        }
        for (int c = dirs.getInt(d + 8); c != -1; ) {
            if (c < 0 || c + 0x18 > dirs.limit()) throw new Corrupt("RomFS directory");
            int nl = dirs.getInt(c + 0x14);
            String n = name(dirs, c + 0x18, nl);
            if (n.isEmpty() || n.equals(".") || n.equals("..") || n.contains("/")) throw new Corrupt("RomFS name");
            walk(dirs, files, c, path.isEmpty() ? n : path + "/" + n, data, out, depth + 1);
            c = dirs.getInt(c + 4);
        }
    }

    // a computer or Termux: java NxPackage.java <game.xci|game.nsp> <prod.keys> <dest folder> (dest "-": only list)
    public static void main(String[] args) throws Exception {
        if (args.length < 3) {
            System.out.println("usage: java NxPackage.java <game.nsp|game.xci> <prod.keys> <dest folder | ->");
            return;
        }
        Map<String, byte[]> k;
        try (InputStream in = new java.io.FileInputStream(args[1])) { k = parseKeys(in); }
        long t0 = System.nanoTime();
        try (FileChannel ch = FileChannel.open(new File(args[0]).toPath())) {
            NxPackage p = new NxPackage(ch, k);
            try {
                p.open();
            } catch (Exception e) {
                System.out.println("ERROR: " + explain(e));
                System.exit(1);
            }
            long total = 0;
            for (RomFile f : p.exefsFiles) total += f.size;
            for (RomFile f : p.romfsFiles) total += f.size;
            System.out.printf("exefs: %d files, romfs: %d files, %.2f GB%n", p.exefsFiles.size(), p.romfsFiles.size(), total / 1e9);
            if (args[2].equals("-")) return;
            File dest = new File(args[2]);
            final long all = total;
            final long[] done = {0};
            LongConsumer prog = n -> { done[0] += n; System.out.printf("\r%.1f / %.1f GB", done[0] / 1e9, all / 1e9); };
            for (RomFile f : p.exefsFiles) p.write(f, new File(dest, "exefs/" + f.path), prog);
            for (RomFile f : p.romfsFiles) p.write(f, new File(dest, "romfs/" + f.path), prog);
            System.out.printf("%ndone in %.1f s%n", (System.nanoTime() - t0) / 1e9);
        }
    }
}

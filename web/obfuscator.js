// Core obfuscation engine using deterministic PRNG.

const AZ = (() => {
  const MAGIC = [0x41, 0x49, 0x21]; // Magic bytes for signal detection.
  const HI = 200, LO = 40, TH = 120; // Signal encoding thresholds.
  const H_SIG = 4; // Metadata signal height.

  // -- Hashing & PRNG --

  // Return SHA-256 hash with fallback.
  async function hash(str) {
    const data = new TextEncoder().encode(str);
    try {
      return new Uint8Array(await crypto.subtle.digest('SHA-256', data));
    } catch (_) {
      const r = new Uint8Array(32);
      for (let i = 0; i < data.length; i++) r[i % 32] = (r[i % 32] * 31 + data[i]) & 0xFF;
      for (let n = 0; n < 8; n++)
        for (let i = 0; i < 32; i++)
          r[i] = (r[i] ^ r[(i + 13) % 32] ^ ((r[(i + 7) % 32] << 3) & 0xFF)) & 0xFF;
      return r;
    }
  }

  // Mulberry32 PRNG returning [0,1).
  function prng(seed) {
    let s = 0;
    for (let i = 0; i < seed.length; i += 4)
      s ^= ((seed[i] << 24) | (seed[i + 1] << 16) | (seed[i + 2] << 8) | seed[i + 3]);
    s = (s >>> 0) || 1;
    return () => {
      s = (s + 0x6D2B79F5) | 0;
      let t = Math.imul(s ^ (s >>> 15), 1 | s);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // -- Permutation --

  // Fisher-Yates shuffle.
  function shuffle(n, rng) {
    const p = Array.from({ length: n }, (_, i) => i);
    for (let i = n - 1; i > 0; i--) {
      const j = (rng() * (i + 1)) | 0;
      [p[i], p[j]] = [p[j], p[i]];
    }
    return p;
  }

  // Compute inverse permutation.
  function invert(p) {
    const inv = new Array(p.length);
    for (let i = 0; i < p.length; i++) inv[p[i]] = i;
    return inv;
  }

  // -- Block Transform Utilities (32-bit, 1-pass) --
  const IS_LE = new Uint8Array(new Uint32Array([0x11223344]).buffer)[0] === 0x44;
  const INV_MASK = IS_LE ? 0x00FFFFFF : 0xFFFFFF00;

  function applyColorTransform(px, inv, ch) {
    if (inv) px ^= INV_MASK;
    if (ch === 1) {
      return IS_LE
        ? (px & 0xFF000000) | ((px >> 8) & 0x0000FFFF) | ((px << 16) & 0x00FF0000)
        : (px & 0x000000FF) | ((px << 8) & 0xFFFF0000) | ((px >> 16) & 0x0000FF00);
    } else if (ch === 2) {
      return IS_LE
        ? (px & 0xFF000000) | ((px << 8) & 0x00FFFF00) | ((px >> 16) & 0x000000FF)
        : (px & 0x000000FF) | ((px >> 8) & 0x00FFFF00) | ((px << 16) & 0xFF000000);
    }
    return px;
  }

  function reverseColorTransform(px, inv, ch) {
    let p = px;
    if (ch === 1) p = applyColorTransform(p, false, 2);
    else if (ch === 2) p = applyColorTransform(p, false, 1);
    if (inv) p ^= INV_MASK;
    return p;
  }

  // -- Signal encoding --
  // Embed 64-bit metadata signal.
  function embedSignal(data, w, h, origW, origH, B, VER) {
    const bytes = [
      MAGIC[0], MAGIC[1], MAGIC[2], VER,
      (origW >> 8) & 0xFF, origW & 0xFF,
      (origH >> 8) & 0xFF, origH & 0xFF,
    ];

    const bits = [];
    for (let byteIdx = 0; byteIdx < 8; byteIdx++) {
      const byte = bytes[byteIdx];
      for (let bitIdx = 0; bitIdx < 8; bitIdx++) {
        bits.push((byte >> (7 - bitIdx)) & 1);
      }
    }

    const step = Math.floor(w / 64);
    for (let bitIdx = 0; bitIdx < 64; bitIdx++) {
      const v = bits[bitIdx] ? HI : LO;
      const startX = bitIdx * step;
      const endX = startX + step;
      for (let row = h - H_SIG; row < h; row++) {
        for (let col = startX; col < endX; col++) {
          const i = (row * w + col) * 4;
          data[i] = v; data[i + 1] = v; data[i + 2] = v; data[i + 3] = 255;
        }
      }
    }
  }

  // Read 64-bit metadata signal.
  function readSignal(data, w, h) {
    if (w < 64 || h < H_SIG) return null;
    const step = Math.floor(w / 64);
    const bits = [];
    for (let bitIdx = 0; bitIdx < 64; bitIdx++) {
      const startX = bitIdx * step;
      const endX = startX + step;
      let sum = 0;
      for (let row = h - H_SIG; row < h; row++) {
        for (let col = startX; col < endX; col++) {
          const i = (row * w + col) * 4;
          sum += (data[i] + data[i + 1] + data[i + 2]) / 3;
        }
      }
      const avg = sum / (step * H_SIG);
      bits.push(avg > TH ? 1 : 0);
    }

    const bytes = new Uint8Array(8);
    for (let byteIdx = 0; byteIdx < 8; byteIdx++) {
      let byte = 0;
      for (let bitIdx = 0; bitIdx < 8; bitIdx++) {
        const bit = bits[byteIdx * 8 + bitIdx];
        byte = (byte << 1) | bit;
      }
      bytes[byteIdx] = byte;
    }

    if (bytes[0] !== MAGIC[0] || bytes[1] !== MAGIC[1] || bytes[2] !== MAGIC[2]) {
      return null;
    }

    const ver = bytes[3];
    const origW = (bytes[4] << 8) | bytes[5];
    const origH = (bytes[6] << 8) | bytes[7];
    const B = (ver === 2) ? 16 : 8;

    return { ver, origW, origH, B };
  }

  // -- Image obfuscation --

  // Obfuscate image with blocks and signal.
  async function obfuscate(srcCanvas, key) {
    if (key === undefined || key === null) key = '';
    const ow = srcCanvas.width, oh = srcCanvas.height;
    const B = (ow >= 1000 && oh >= 1000) ? 16 : 8;
    const VER = (B === 16) ? 2 : 1;
    const nw = Math.max(Math.ceil(ow / B) * B, 64);
    const nh = Math.ceil(oh / B) * B + H_SIG;

    const c = document.createElement('canvas');
    c.width = nw; c.height = nh;
    const ctx = c.getContext('2d');
    ctx.fillStyle = '#000';
    ctx.fillRect(0, 0, nw, nh);
    ctx.drawImage(srcCanvas, 0, 0);

    const ch = nh - H_SIG; // Content height.
    const id = ctx.getImageData(0, 0, nw, ch);
    const d = id.data;
    const seed = await hash(key);
    const rng = prng(seed);
    const bw = nw / B, n = bw * (ch / B);

    // Generate transforms.
    const xforms = [];
    for (let i = 0; i < n; i++)
      xforms.push({ inv: rng() > 0.5, ch: (rng() * 3) | 0, sp: (rng() * 4) | 0, fl: rng() > 0.5 });

    const perm = shuffle(n, rng);

    // Transform and write blocks in 1-pass.
    const rd = new Uint8ClampedArray(d.length);
    const src32 = new Uint32Array(d.buffer, d.byteOffset, d.byteLength / 4);
    const dst32 = new Uint32Array(rd.buffer, rd.byteOffset, rd.byteLength / 4);

    for (let i = 0; i < n; i++) {
      const S = perm[i], D = i;
      const t = xforms[S];
      const sbx = S % bw, sby = (S / bw) | 0;
      const dbx = D % bw, dby = (D / bw) | 0;

      for (let y = 0; y < B; y++) {
        for (let x = 0; x < B; x++) {
          const si = (sby * B + y) * nw + (sbx * B + x);
          let px = src32[si];

          px = applyColorTransform(px, t.inv, t.ch);

          let cx = x, cy = y;
          for (let r = 0; r < t.sp; r++) {
            let nx = B - 1 - cy;
            cy = cx; cx = nx;
          }
          if (t.fl) cx = B - 1 - cx;

          const di = (dby * B + cy) * nw + (dbx * B + cx);
          dst32[di] = px;
        }
      }
    }

    ctx.putImageData(new ImageData(rd, nw, ch), 0, 0);
    const full = ctx.getImageData(0, 0, nw, nh);
    embedSignal(full.data, nw, nh, ow, oh, B, VER);
    ctx.putImageData(full, 0, 0);
    return c;
  }

  // Deobfuscate image.
  async function deobfuscate(srcCanvas, key) {
    if (key === undefined || key === null) key = '';
    const w = srcCanvas.width, h = srcCanvas.height;
    const ctx = srcCanvas.getContext('2d');

    const full = ctx.getImageData(0, 0, w, h);
    const sig = readSignal(full.data, w, h);
    if (!sig) throw new Error('No signal found');

    const B = sig.B;
    const ch = h - H_SIG;
    const d = ctx.getImageData(0, 0, w, ch).data;
    const seed = await hash(key);
    const rng = prng(seed);
    const bw = w / B, n = bw * (ch / B);

    // Replay PRNG sequence.
    const xforms = [];
    for (let i = 0; i < n; i++)
      xforms.push({ inv: rng() > 0.5, ch: (rng() * 3) | 0, sp: (rng() * 4) | 0, fl: rng() > 0.5 });
    const perm = shuffle(n, rng);
    const inv = invert(perm);

    // Reverse transforms and unshuffle blocks in 1-pass.
    const rd = new Uint8ClampedArray(d.length);
    const src32 = new Uint32Array(d.buffer, d.byteOffset, d.byteLength / 4);
    const dst32 = new Uint32Array(rd.buffer, rd.byteOffset, rd.byteLength / 4);

    for (let j = 0; j < n; j++) {
      const S = inv[j], D = j;
      const t = xforms[j];
      const sbx = S % bw, sby = (S / bw) | 0;
      const dbx = D % bw, dby = (D / bw) | 0;
      
      const rot = (4 - t.sp) % 4;

      for (let y = 0; y < B; y++) {
        for (let x = 0; x < B; x++) {
          const si = (sby * B + y) * w + (sbx * B + x);
          let px = src32[si];

          let cx = x, cy = y;
          if (t.fl) cx = B - 1 - cx;
          for (let r = 0; r < rot; r++) {
            let nx = B - 1 - cy;
            cy = cx; cx = nx;
          }

          px = reverseColorTransform(px, t.inv, t.ch);

          const di = (dby * B + cy) * w + (dbx * B + cx);
          dst32[di] = px;
        }
      }
    }

    // Crop to original size.
    const tmp = document.createElement('canvas');
    tmp.width = w; tmp.height = ch;
    tmp.getContext('2d').putImageData(new ImageData(rd, w, ch), 0, 0);
    const out = document.createElement('canvas');
    out.width = sig.origW; out.height = sig.origH;
    out.getContext('2d').drawImage(tmp, 0, 0, sig.origW, sig.origH, 0, 0, sig.origW, sig.origH);
    return out;
  }

  // Detect signal in image.
  async function detect(imgOrCanvas) {
    const c = document.createElement('canvas');
    if (imgOrCanvas instanceof HTMLCanvasElement) {
      c.width = imgOrCanvas.width; c.height = imgOrCanvas.height;
      c.getContext('2d').drawImage(imgOrCanvas, 0, 0);
    } else {
      c.width = imgOrCanvas.naturalWidth || imgOrCanvas.width;
      c.height = imgOrCanvas.naturalHeight || imgOrCanvas.height;
      c.getContext('2d').drawImage(imgOrCanvas, 0, 0);
    }
    return readSignal(c.getContext('2d').getImageData(0, 0, c.width, c.height).data, c.width, c.height);
  }

  // -- Text obfuscation --

  // Convert bytes to base64.
  function bytesToBase64(bytes) {
    let bin = '';
    for (let i = 0; i < bytes.length; i++) bin += String.fromCharCode(bytes[i]);
    return btoa(bin);
  }

  // Convert base64 to bytes.
  function base64ToBytes(b64) {
    const clean = b64.replace(/[^A-Za-z0-9+/=]/g, '');
    const bin = atob(clean);
    const out = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
    return out;
  }

  // Obfuscate text.
  async function obfuscateText(text, key) {
    if (key === undefined || key === null) key = '';
    const seed = await hash(key);
    const rng = prng(seed);
    const data = new TextEncoder().encode(text);
    const out = new Uint8Array(data.length);
    for (let i = 0; i < data.length; i++) {
      const xv = (rng() * 256) | 0;
      const r = (rng() * 8) | 0;
      let b = data[i] ^ xv;
      b = ((b << r) | (b >>> (8 - r))) & 0xFF;
      out[i] = b;
    }
    return `AI!1(${bytesToBase64(out)})`;
  }

  // Deobfuscate text.
  async function deobfuscateText(str, key) {
    if (key === undefined || key === null) key = '';
    const match = str.match(/AI!1\(([^)]+)\)/);
    if (!match) throw new Error('No AI!1(...) signature found');
    const data = base64ToBytes(match[1]);
    const seed = await hash(key);
    const rng = prng(seed);
    const out = new Uint8Array(data.length);
    for (let i = 0; i < data.length; i++) {
      const xv = (rng() * 256) | 0;
      const r = (rng() * 8) | 0;
      let b = data[i];
      b = ((b >>> r) | (b << (8 - r))) & 0xFF;
      b = b ^ xv;
      out[i] = b;
    }
    return new TextDecoder().decode(out);
  }

  return { obfuscate, deobfuscate, detect, readSignal, obfuscateText, deobfuscateText };
})();

// Tiny stack VM for make.fun tiny-stack-vm-01-run-20261122. Pre-decoded
// (threaded) dispatch: every byte position is decoded once into an op id +
// immediate, so the hot loop never re-reads immediates or re-checks validity,
// and a jump into an immediate decodes as the reference VM would fetch it.
// Stack/memory are Int32Arrays (real 32-bit ints, no boxing). Semantics follow
// ISA.md and vm.mjs literally: same trap codes, check order and arithmetic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [byte, pops, pushes, immediate bytes]
const SPEC = [
  [0x00, 0, 0, 0], [0x01, 0, 1, 1], [0x02, 0, 1, 4], [0x03, 1, 0, 0], [0x04, 1, 2, 0],
  [0x05, 2, 2, 0], [0x06, 2, 3, 0], [0x07, 3, 3, 0], [0x10, 2, 1, 0], [0x11, 2, 1, 0],
  [0x12, 2, 1, 0], [0x13, 2, 1, 0], [0x14, 2, 1, 0], [0x15, 2, 1, 0], [0x16, 2, 1, 0],
  [0x17, 1, 1, 0], [0x18, 2, 1, 0], [0x19, 2, 1, 0], [0x1a, 2, 1, 0], [0x1b, 1, 1, 0],
  [0x1c, 2, 1, 0], [0x1d, 2, 1, 0], [0x1e, 2, 1, 0], [0x20, 2, 1, 0], [0x21, 2, 1, 0],
  [0x22, 2, 1, 0], [0x30, 0, 0, 2], [0x31, 1, 0, 2], [0x32, 1, 0, 2], [0x33, 0, 0, 2],
  [0x34, 0, 0, 0], [0x40, 1, 1, 0], [0x41, 2, 0, 0], [0x50, 1, 0, 0], [0x51, 1, 0, 0],
  [0x52, 0, 1, 0], [0x53, 1, 0, 0],
];
const POPS = new Int8Array(256).fill(-1);
const PUSH = new Int8Array(256);
const IMM = new Int8Array(256);
for (const [b, po, pu, im] of SPEC) { POPS[b] = po; PUSH[b] = pu; IMM[b] = im; }
const BAD = 0xF0, PCT = 0xF1;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const op = new Uint8Array(n);
  const arg = new Int32Array(n);
  for (let i = 0; i < n; i++) {
    const b = p[i];
    if (POPS[b] < 0) { op[i] = BAD; continue; }
    const im = IMM[b];
    if (i + im >= n) { op[i] = PCT; continue; }
    op[i] = b;
    if (im === 1) arg[i] = (p[i + 1] << 24) >> 24;
    else if (im === 4) arg[i] = p[i + 1] | (p[i + 2] << 8) | (p[i + 3] << 16) | (p[i + 4] << 24);
    else if (im === 2) arg[i] = b === 0x33 ? p[i + 1] | (p[i + 2] << 8) : ((p[i + 1] | (p[i + 2] << 8)) << 16) >> 16;
  }
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: out.subarray(0, olen), code });
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const o = op[pc];
    if (o === BAD) return end(5);
    if (o === PCT) return end(9);
    const pp = POPS[o];
    steps++;
    if (sp < pp) return end(2);
    if (sp - pp + PUSH[o] > 256) return end(3);
    const a = arg[pc];
    pc += 1 + IMM[o];
    switch (o) {
      case 0x00: return end(0);
      case 0x01: case 0x02: D[sp++] = a; break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const t = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = t; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e: case 0x20:
      case 0x21: case 0x22: {
        const b = D[sp - 1], x = D[sp - 2];
        let r: number;
        // Chain ordered by measured frequency on the practice set
        // (LT 19,079; SUB 15,659; ADD 14,183; MOD 3,723; MUL 2,924; EQ 2,045;
        // DIV 934; LTU 519; SHRU 350; XOR 269; AND 258; SHL 178; SHR 14;
        // DIVU 6; MODU 6; OR 4 of 467,964 steps), so the common ops test first.
        if (o === 0x21) r = x < b ? 1 : 0;
        else if (o === 0x11) r = (x - b) | 0;
        else if (o === 0x10) r = (x + b) | 0;
        else if (o === 0x14) { if (b === 0) return end(4); r = b === -1 ? 0 : (x % b) | 0; }
        else if (o === 0x12) r = Math.imul(x, b);
        else if (o === 0x20) r = x === b ? 1 : 0;
        else if (o === 0x13) { if (b === 0) return end(4); r = x === -2147483648 && b === -1 ? x : (x / b) | 0; }
        else if (o === 0x22) r = (x >>> 0) < (b >>> 0) ? 1 : 0;
        else if (o === 0x1e) r = (x >>> (b & 31)) | 0;
        else if (o === 0x1a) r = x ^ b;
        else if (o === 0x18) r = x & b;
        else if (o === 0x1c) r = x << (b & 31);
        else if (o === 0x1d) r = x >> (b & 31);
        else if (o === 0x15) { if (b === 0) return end(4); r = Math.floor((x >>> 0) / (b >>> 0)) | 0; }
        else if (o === 0x16) { if (b === 0) return end(4); r = ((x >>> 0) % (b >>> 0)) | 0; }
        else r = x | b;
        D[sp - 2] = r; sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        let take = true;
        if (o !== 0x30) { const v = D[--sp]; take = o === 0x31 ? v === 0 : v !== 0; }
        if (take) pc += a;
        break;
      }
      case 0x33:
        if (csp === 64) return end(7);
        C[csp++] = pc;
        pc = a;
        break;
      case 0x34:
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= 256) return end(6);
        sp -= 2; M[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let k = 0; k < s.length; k++) out[olen++] = s.charCodeAt(k);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return end(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return end(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}

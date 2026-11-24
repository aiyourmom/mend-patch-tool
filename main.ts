// main.ts is mend, the CLI SPEC.md specifies. It does all ten sections of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, three-tier line matching, unified diffs, SEARCH/REPLACE blocks, V4A
// patches, JSON edits and the all-or-nothing write. Node 22, the standard library alone; run it as
// `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** What the format parsers share: strict matching, and the move pairs for the R output lines. */
interface Ctx {
  strict: boolean;
  moves: Array<[string, string]>;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------------------------------------------------------------------------
// Section 3: a file's lines, its line break, and whether it ends with one.
// ---------------------------------------------------------------------------

interface FileLines {
  lines: string[];
  br: string;
  final: boolean;
}

function splitFile(text: string): FileLines {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}

function joinFile(f: FileLines): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

// ---------------------------------------------------------------------------
// Section 5: matching lines at three tiers, and building the replacement.
// ---------------------------------------------------------------------------

const rstripWS = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWS = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWS = (s: string): string => /^[ \t]*/.exec(s)![0];

/** Positions i where O matches lines[i .. i+O.length-1] at the given tier, starting at `from`. */
function findOcc(lines: string[], O: string[], tier: number, from: number): number[] {
  const eq =
    tier === 0 ? (a: string, b: string): boolean => a === b
    : tier === 1 ? (a: string, b: string): boolean => rstripWS(a) === rstripWS(b)
    : (a: string, b: string): boolean => trimWS(a) === trimWS(b);
  const out: number[] = [];
  for (let i = from; i + O.length <= lines.length; i++) {
    let ok = true;
    for (let k = 0; k < O.length; k++) {
      if (!eq(lines[i + k]!, O[k]!)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/**
 * The first tier (0, then 1, then 2; only 0 with --strict) at which O occurs at least once at or after
 * `from`, with its positions. With eofOnly, only occurrences ending at the file's last line count.
 */
function findTiered(
  lines: string[],
  O: string[],
  strict: boolean,
  from: number,
  eofOnly = false,
): { tier: number; positions: number[] } | null {
  if (O.length === 0) return null;
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    let pos = findOcc(lines, O, tier, from);
    if (eofOnly) pos = pos.filter((p) => p + O.length === lines.length);
    if (pos.length > 0) return { tier, positions: pos };
  }
  return null;
}

/** Old lines O and new lines N of a hunk/chunk/block; N entries that are context lines name their O index. */
interface OldNew {
  O: string[];
  N: Array<{ text: string; oIdx: number | null }>;
}

/**
 * The lines that replace the matched ones: a context line is written as the file's own matched line, never the
 * patch's; at tier 2 every other line is re-indented from O's first line's leading whitespace to the file's.
 */
function buildReplacement(h: OldNew, fileLines: string[], at: number, tier: number): string[] {
  const P = h.O.length > 0 ? leadWS(h.O[0]!) : '';
  const F = leadWS(fileLines[at]!);
  return h.N.map((e) => {
    if (e.oIdx !== null) return fileLines[at + e.oIdx]!;
    if (tier !== 2) return e.text;
    const t = e.text;
    if (t === '' || /^[ \t]*$/.test(t)) return t;
    return t.startsWith(P) ? F + t.slice(P.length) : t;
  });
}

// ---------------------------------------------------------------------------
// Section 9: JSON edits (one JSON array of edit objects, or JSON Lines).
// ---------------------------------------------------------------------------

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------------------------------------------------------------------------
// Section 6: unified diffs.
// ---------------------------------------------------------------------------

interface UHunk extends OldNew {
  a: number;
  /** A `\` line follows the hunk's last context or `+` line. */
  bsAfterLast: boolean;
  /** A `\` line follows the hunk's last `+` line (false if it has none). Creation rule, section 6. */
  bsAfterLastPlus: boolean;
}

interface USection {
  dashOld: string | null | undefined;
  dashNew: string | null | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  gitOld: string | undefined;
  gitNew: string | undefined;
  create: boolean;
  del: boolean;
  hunks: UHunk[];
  oldPath: string | null;
  newPath: string | null;
}

/** The path of a `--- ` / `+++ ` header line: text after the four characters, up to the first tab, trimmed. */
function dashPath(line: string): string | null {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

function parseDiffGit(line: string, i: number): [string, string] {
  const rest = line.slice('diff --git '.length).trimEnd();
  if (!rest.startsWith('a/')) throw new Exit2(`error: parse ${i + 1}`);
  const sep = rest.indexOf(' b/', 2);
  if (sep < 0) throw new Exit2(`error: parse ${i + 1}`);
  const x = rest.slice(2, sep);
  const y = rest.slice(sep + 3);
  if (x === '' || y === '') throw new Exit2(`error: parse ${i + 1}`);
  return [x, y];
}

/**
 * A section's header lines: `--- ` / `+++ `, `rename from` / `rename to`, `new file mode`, `deleted file
 * mode`; everything else is ignored. Stops at the first hunk, the next section, or the end of the patch.
 */
function parseUnifiedHeader(lines: string[], i: number, s: USection): number {
  let haveDash = false;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('@@') || line.startsWith('diff --git ')) return i;
    if (line.startsWith('--- ')) {
      const next = lines[i + 1];
      if (next === undefined || !next.startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
      if (haveDash) return i;
      s.dashOld = dashPath(line);
      s.dashNew = dashPath(next);
      haveDash = true;
      i += 2;
      continue;
    }
    if (line.startsWith('rename from ')) {
      s.renameFrom = line.slice('rename from '.length).trim();
      i++;
      continue;
    }
    if (line.startsWith('rename to ')) {
      s.renameTo = line.slice('rename to '.length).trim();
      i++;
      continue;
    }
    if (line === 'new file mode' || line.startsWith('new file mode ')) {
      s.create = true;
      i++;
      continue;
    }
    if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) {
      s.del = true;
      i++;
      continue;
    }
    i++;
  }
  return i;
}

/** One hunk: its header, its body, and the line after the body. */
function parseHunk(lines: string[], i: number): { hunk: UHunk; next: number } {
  const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(lines[i]!);
  if (m === null) throw new Exit2(`error: parse ${i + 1}`);
  const a = parseInt(m[1]!, 10);
  let j = i + 1;
  const body: string[] = [];
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+' || l[0] === '\\') {
      body.push(l);
      j++;
      continue;
    }
    break;
  }
  while (body.length > 0 && body[body.length - 1] === '') body.pop();
  const O: string[] = [];
  const N: Array<{ text: string; oIdx: number | null }> = [];
  let lastCtxPlus = -1;
  let lastPlusIdx = -1;
  for (let k = 0; k < body.length; k++) {
    const l = body[k]!;
    if (l[0] === ' ') {
      O.push(l.slice(1));
      N.push({ text: l.slice(1), oIdx: O.length - 1 });
      lastCtxPlus = k;
    } else if (l[0] === '-') {
      O.push(l.slice(1));
    } else if (l[0] === '+') {
      N.push({ text: l.slice(1), oIdx: null });
      lastCtxPlus = k;
      lastPlusIdx = k;
    } else if (l === '') {
      O.push('');
      N.push({ text: '', oIdx: O.length - 1 });
      lastCtxPlus = k;
    }
    // A `\` line refers to the body line before it and is otherwise ignored here.
  }
  const bsAfterLast = lastCtxPlus >= 0 && body[lastCtxPlus + 1] !== undefined && body[lastCtxPlus + 1]![0] === '\\';
  const bsAfterLastPlus = lastPlusIdx >= 0 && body[lastPlusIdx + 1] !== undefined && body[lastPlusIdx + 1]![0] === '\\';
  return { hunk: { a, O, N, bsAfterLast, bsAfterLastPlus }, next: j };
}

function parseUnifiedSections(lines: string[]): USection[] {
  const sections: USection[] = [];
  const fresh = (): USection => ({
    dashOld: undefined,
    dashNew: undefined,
    renameFrom: undefined,
    renameTo: undefined,
    gitOld: undefined,
    gitNew: undefined,
    create: false,
    del: false,
    hunks: [],
    oldPath: null,
    newPath: null,
  });
  let cur: USection | null = null;
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const [x, y] = parseDiffGit(line, i);
      cur = fresh();
      cur.gitOld = x;
      cur.gitNew = y;
      sections.push(cur);
      i++;
      i = parseUnifiedHeader(lines, i, cur);
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      cur = fresh();
      sections.push(cur);
      i = parseUnifiedHeader(lines, i, cur);
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const r = parseHunk(lines, i);
      cur.hunks.push(r.hunk);
      i = r.next;
      continue;
    }
    i++;
  }
  // Resolve each section's paths: `---`/`+++` first, then `rename from`/`to`, then `diff --git`.
  const norm = (p: string | undefined): string | null | undefined =>
    p === undefined ? undefined : p === '/dev/null' ? null : p;
  const pick = (a: string | null | undefined, b: string | undefined, c: string | undefined): string | null =>
    a !== undefined ? a : b !== undefined ? (norm(b) ?? null) : (norm(c) ?? null);
  for (const s of sections) {
    s.oldPath = pick(s.dashOld, s.renameFrom, s.gitOld);
    s.newPath = pick(s.dashNew, s.renameTo, s.gitNew);
  }
  return sections;
}

/** Apply a section's hunks in order to a file's lines, tracking the final line break per section 6. */
function applyUnifiedHunks(f: FileLines, hunks: UHunk[], strict: boolean, path: string): FileLines {
  let cur = f.lines;
  let curFinal = f.final;
  let d = 0;
  for (const h of hunks) {
    if (h.O.length === 0) {
      const atEnd = h.a + d >= cur.length;
      const ins = Math.max(0, Math.min(h.a + d, cur.length));
      const add = h.N.map((e) => e.text);
      cur = cur.slice(0, ins).concat(add, cur.slice(ins));
      if (atEnd) curFinal = !h.bsAfterLast;
    } else {
      const found = findTiered(cur, h.O, strict, 0);
      if (found === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let best = found.positions[0]!;
      for (const p of found.positions) {
        if (Math.abs(p - target) < Math.abs(best - target)) best = p;
      }
      const repl = buildReplacement(h, cur, best, found.tier);
      const atEnd = best + h.O.length === cur.length;
      cur = cur.slice(0, best).concat(repl, cur.slice(best + h.O.length));
      if (atEnd) curFinal = !h.bsAfterLast;
    }
    d += h.N.length - h.O.length;
  }
  return { lines: cur, br: f.br, final: curFinal };
}

function unifiedEdits(lines: string[], ctx: Ctx): Edit[] {
  const sections = parseUnifiedSections(lines);
  return sections.map((s) => {
    const oldPath = s.oldPath;
    const newPath = s.newPath;
    const isCreate = s.create || oldPath === null;
    const isDelete = !isCreate && (s.del || newPath === null);
    const isMove =
      !isCreate && !isDelete && oldPath !== null && newPath !== null && oldPath !== newPath;
    return (tree: Tree) => {
      if (oldPath !== null && !safe(oldPath)) throw new Fail('unsafe', oldPath);
      if (newPath !== null && newPath !== oldPath && !safe(newPath)) throw new Fail('unsafe', newPath);
      if (isCreate) {
        if (newPath === null) throw new Fail('unsafe', '/dev/null');
        if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
        const plus: string[] = [];
        let lastPlus: UHunk | null = null;
        for (const h of s.hunks) {
          const linesPlus = h.N.filter((e) => e.oIdx === null).map((e) => e.text);
          if (linesPlus.length > 0) lastPlus = h;
          plus.push(...linesPlus);
        }
        const finalBreak = lastPlus === null ? true : !lastPlus.bsAfterLastPlus;
        tree.now.set(newPath, plus.length === 0 ? '' : plus.join('\n') + (finalBreak ? '\n' : ''));
        return;
      }
      if (isDelete) {
        if (oldPath === null) throw new Fail('unsafe', '/dev/null');
        if (tree.get(oldPath) === null) throw new Fail('missing', oldPath);
        tree.now.set(oldPath, null);
        return;
      }
      if (oldPath === null) throw new Fail('unsafe', '/dev/null');
      const before = tree.get(oldPath);
      if (before === null) throw new Fail('missing', oldPath);
      if (isMove) {
        if (newPath === null) throw new Fail('unsafe', '/dev/null');
        if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
      }
      const out = applyUnifiedHunks(splitFile(before), s.hunks, ctx.strict, oldPath);
      const text = joinFile(out);
      if (isMove) {
        tree.now.set(oldPath, null);
        tree.now.set(newPath!, text);
        ctx.moves.push([oldPath, newPath!]);
      } else {
        tree.now.set(oldPath, text);
      }
    };
  });
}

// ---------------------------------------------------------------------------
// Section 7: SEARCH/REPLACE blocks.
// ---------------------------------------------------------------------------

function searchReplaceEdits(lines: string[], ctx: Ctx): Edit[] {
  const edits: Edit[] = [];
  let i = 0;
  let prevReplaceEnd = -1;
  let prevPath: string | null = null;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let k = searchLine - 1; k > prevReplaceEnd; k--) {
      const l = lines[k]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new Exit2(`error: parse ${searchLine + 1}`);
    let sep = -1;
    for (let k = searchLine + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '=======') {
        sep = k;
        break;
      }
    }
    if (sep < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    let rep = -1;
    for (let k = sep + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = k;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    const oldLines = lines.slice(searchLine + 1, sep);
    const newLines = lines.slice(sep + 1, rep);
    edits.push(((p, o, n) => (tree: Tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (o.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, n.length === 0 ? '' : n.join('\n') + '\n');
        return;
      }
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const f = splitFile(before);
      const found = findTiered(f.lines, o, ctx.strict, 0);
      if (found === null) throw new Fail('no-match', p);
      if (found.positions.length !== 1) throw new Fail('ambiguous', p);
      const at = found.positions[0]!;
      const repl = buildReplacement(
        { O: o, N: n.map((t) => ({ text: t, oIdx: null })) },
        f.lines,
        at,
        found.tier,
      );
      const out = f.lines.slice(0, at).concat(repl, f.lines.slice(at + o.length));
      tree.now.set(p, joinFile({ lines: out, br: f.br, final: f.final }));
    })(path, oldLines, newLines));
    prevPath = path;
    prevReplaceEnd = rep;
    i = rep + 1;
  }
  return edits;
}

// ---------------------------------------------------------------------------
// Section 8: V4A patches.
// ---------------------------------------------------------------------------

interface VChunk extends OldNew {
  anchor: string | null;
  eof: boolean;
}

const V4A_SECTION = /^(\*\*\* (?:Add|Delete|Update) File: )/;
const isV4aSectionStart = (l: string): boolean =>
  l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
const isV4aBodyLine = (l: string): boolean => l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+';

function buildChunkBody(body: string[]): OldNew {
  const O: string[] = [];
  const N: Array<{ text: string; oIdx: number | null }> = [];
  for (const l of body) {
    if (l[0] === ' ') {
      O.push(l.slice(1));
      N.push({ text: l.slice(1), oIdx: O.length - 1 });
    } else if (l[0] === '-') {
      O.push(l.slice(1));
    } else if (l[0] === '+') {
      N.push({ text: l.slice(1), oIdx: null });
    } else if (l === '') {
      O.push('');
      N.push({ text: '', oIdx: O.length - 1 });
    }
  }
  return { O, N };
}

/** Parse an Update File section's raw lines (trailing blank lines already removed) into Move to + chunks. */
function parseV4aUpdate(raw: string[], base: number): { moveTo: string | null; chunks: VChunk[] } {
  let idx = 0;
  let moveTo: string | null = null;
  if (raw.length > 0 && raw[0]!.startsWith('*** Move to: ')) {
    moveTo = raw[0]!.slice('*** Move to: '.length).trim();
    idx = 1;
  }
  const chunks: VChunk[] = [];
  let cur: { anchor: string | null; eof: boolean; body: string[] } | null = null;
  for (let k = idx; k < raw.length; k++) {
    const l = raw[k]!;
    const no = base + k;
    if (l.startsWith('@@')) {
      cur = { anchor: l.slice(2).trim(), eof: false, body: [] };
      chunks.push(cur as unknown as VChunk);
      continue;
    }
    if (l === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${no}`);
      cur.eof = true;
      cur = null;
      continue;
    }
    if (l.startsWith('***')) throw new Exit2(`error: parse ${no}`);
    if (cur === null) {
      if (chunks.length > 0) throw new Exit2(`error: parse ${no}`);
      if (!isV4aBodyLine(l)) throw new Exit2(`error: parse ${no}`);
      cur = { anchor: null, eof: false, body: [] };
      chunks.push(cur as unknown as VChunk);
    }
    if (!isV4aBodyLine(l)) throw new Exit2(`error: parse ${no}`);
    cur.body.push(l);
  }
  const out: VChunk[] = [];
  for (const c of chunks as unknown as Array<{ anchor: string | null; eof: boolean; body: string[] }>) {
    const r = buildChunkBody(c.body);
    out.push({ anchor: c.anchor, eof: c.eof, O: r.O, N: r.N });
  }
  return { moveTo, chunks: out };
}

function v4aEdits(lines: string[], ctx: Ctx): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    const addM = /^\*\*\* Add File: (.*)$/.exec(line);
    const delM = /^\*\*\* Delete File: (.*)$/.exec(line);
    const updM = /^\*\*\* Update File: (.*)$/.exec(line);
    if (addM === null && delM === null && updM === null) throw new Exit2(`error: parse ${i + 1}`);
    const rawStart = i + 1;
    let j = rawStart;
    while (j < last && !isV4aSectionStart(lines[j]!)) j++;
    const raw = lines.slice(rawStart, j);
    while (raw.length > 0 && blank(raw[raw.length - 1]!)) raw.pop();
    if (addM !== null) {
      const path = addM[1]!.trim();
      const fileLines: string[] = [];
      for (let k = 0; k < raw.length; k++) {
        const l = raw[k]!;
        if (l.startsWith('+')) fileLines.push(l.slice(1));
        else if (l === '') fileLines.push('');
        else throw new Exit2(`error: parse ${rawStart + k + 1}`);
      }
      edits.push(((p, fl) => (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, fl.length === 0 ? '' : fl.join('\n') + '\n');
      })(path, fileLines));
    } else if (delM !== null) {
      const path = delM[1]!.trim();
      if (raw.length > 0) throw new Exit2(`error: parse ${rawStart + 1}`);
      edits.push(((p) => (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      })(path));
    } else {
      const path = updM![1]!.trim();
      const { moveTo, chunks } = parseV4aUpdate(raw, rawStart + 1);
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${i + 1}`);
      edits.push(((p, mv, ch) => (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (mv !== null && !safe(mv)) throw new Fail('unsafe', mv);
        const before = tree.get(p);
        if (before === null) throw new Fail('missing', p);
        if (mv !== null && tree.get(mv) !== null) throw new Fail('exists', mv);
        const f = splitFile(before);
        let cur = f.lines;
        let cursor = 0;
        for (const chunk of ch) {
          if (chunk.anchor !== null && chunk.anchor !== '') {
            const found = findTiered(cur, [chunk.anchor], ctx.strict, cursor);
            if (found === null) throw new Fail('no-match', p);
            cursor = found.positions[0]! + 1;
          }
          if (chunk.O.length === 0) {
            const ins = chunk.eof ? cur.length : cursor;
            const add = chunk.N.map((e) => e.text);
            cur = cur.slice(0, ins).concat(add, cur.slice(ins));
            cursor = ins + add.length;
          } else {
            const found = findTiered(cur, chunk.O, ctx.strict, cursor, chunk.eof);
            if (found === null) throw new Fail('no-match', p);
            const at = found.positions[0]!;
            const repl = buildReplacement(chunk, cur, at, found.tier);
            cur = cur.slice(0, at).concat(repl, cur.slice(at + chunk.O.length));
            cursor = at + repl.length;
          }
        }
        const text = joinFile({ lines: cur, br: f.br, final: f.final });
        if (mv !== null) {
          tree.now.set(p, null);
          tree.now.set(mv, text);
          ctx.moves.push([p, mv]);
        } else {
          tree.now.set(p, text);
        }
      })(path, moveTo, chunks));
    }
    i = j;
  }
  return edits;
}

// ---------------------------------------------------------------------------
// Sections 1, 2 and 10: invocation, output and exit codes, order and atomicity.
// ---------------------------------------------------------------------------

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  const ctx: Ctx = { strict, moves: [] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, ctx)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, ctx)
            : v4aEdits(lines, ctx);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const changed: string[] = [];
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    changed.push(p);
    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  const rowByPath = new Map<string, string>();
  for (const p of changed) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    rowByPath.set(p, was === null ? 'A' : now === null ? 'D' : 'M');
  }
  const rows: Array<{ key: string; text: string }> = [];
  for (const [o, n] of ctx.moves) {
    if (rowByPath.get(o) === 'D' && rowByPath.get(n) === 'A') {
      rowByPath.delete(o);
      rowByPath.delete(n);
      rows.push({ key: n, text: `R ${o} -> ${n}` });
    }
  }
  for (const [p, k] of rowByPath) rows.push({ key: p, text: `${k} ${p}` });
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}

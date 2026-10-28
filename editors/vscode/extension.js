// Formats a Hailperin file with `hailperin fmt`, and indents as you type the way fmt lays a file
// out: a block one level in, the line after a finished `therefore` one level out, the rest of an
// item two levels past its start, and a `by` on its own line in its segment's column.
const vscode = require('vscode');
const { spawnSync } = require('child_process');

const LEVEL = 2;

// Whether a line starts an item: a label, a keyword that opens one, or a comment.
const startsItem = (line) =>
  /^\s*([a-z][A-Za-z0-9_]*\s*:|--|(theorem|lemma|define|import|predicate|variable|assume|therefore)\b)/.test(line);

// Whether a line, without its comment, leaves its formula unfinished.
function unfinished(line) {
  const code = line.replace(/\s*--.*$/, '');
  const open = (code.match(/\(/g) || []).length - (code.match(/\)/g) || []).length;
  return /(->|\band|\bor|\bnot|\.)\s*$/.test(code) || open > 0;
}

const indentOf = (line) => line.match(/^\s*/)[0].length;
const blank = (line) => !/\S/.test(line);

function prevNonblank(lines, n) {
  let i = n - 1;
  while (i >= 0 && blank(lines[i])) i--;
  return i;
}

// The first line of the item line `n` belongs to.
function itemStart(lines, n) {
  while (n > 0 && !startsItem(lines[n])) n = prevNonblank(lines, n);
  return Math.max(n, 0);
}

// The column of the nearest `by` after other text among the items indented `base` around line
// `n`, above it first, then below, without crossing a lemma: the segment's column.
function byColumn(lines, n, base) {
  for (const step of [-1, 1]) {
    for (let i = n + step; i >= 0 && i < lines.length; i += step) {
      if (blank(lines[i])) continue;
      const indent = indentOf(lines[itemStart(lines, i)]);
      if (indent < base || (indent === base && /^\s*lemma\b/.test(lines[i]))) break;
      const m = lines[i].match(/^(.*\S\s+)by\b/);
      if (m && indent === base) return m[1].length;
    }
  }
  return -1;
}

// The indentation of line `n`.
function indentFor(lines, n) {
  const prev = prevNonblank(lines, n);
  const line = lines[n];
  if (prev < 0 || /^\s*(theorem|define|import)\b/.test(line)) return 0;
  const start = itemStart(lines, prev);
  const base = indentOf(lines[start]);
  // A line that doesn't start an item goes on with the one above. On a fresh line, only an
  // unfinished formula says so.
  const goesOn = blank(line) ? unfinished(lines[prev]) : !startsItem(line);
  if (goesOn) {
    const by = /^\s*by\b/.test(line) ? byColumn(lines, n, base) : -1;
    return by >= 0 ? by : base + 2 * LEVEL;
  }
  const first = lines[start];
  if (/^\s*(theorem|lemma)\b.*:\s*(--.*)?$/.test(first)) return base + LEVEL;
  if (/^\s*therefore\b/.test(first)) return Math.max(base - LEVEL, 0);
  return base;
}

function activate(context) {
  const formatter = {
    provideDocumentFormattingEdits(document) {
      const cmd = vscode.workspace.getConfiguration('hailperin').get('path', 'hailperin');
      const run = spawnSync(cmd, ['fmt', '-'], { input: document.getText(), encoding: 'utf8' });
      if (run.error || run.status !== 0) {
        const why = run.error ? run.error.message : (run.stdout + run.stderr).trim();
        vscode.window.showErrorMessage(`hailperin fmt: ${why}`);
        return [];
      }
      const all = new vscode.Range(document.positionAt(0), document.positionAt(document.getText().length));
      return [vscode.TextEdit.replace(all, run.stdout)];
    },
  };
  // On Enter, the new line; on a space after a `by` that starts a line, that line.
  const indenter = {
    provideOnTypeFormattingEdits(document, position, ch) {
      const n = position.line;
      const text = document.lineAt(n).text;
      if (ch === ' ' && !/^\s*by $/.test(text.slice(0, position.character))) return [];
      const lines = [];
      for (let i = 0; i < document.lineCount; i++) lines.push(document.lineAt(i).text);
      const want = indentFor(lines, n);
      const have = indentOf(text);
      if (want === have) return [];
      return [vscode.TextEdit.replace(new vscode.Range(n, 0, n, have), ' '.repeat(want))];
    },
  };
  context.subscriptions.push(
    vscode.languages.registerDocumentFormattingEditProvider('hailperin', formatter),
    vscode.languages.registerOnTypeFormattingEditProvider('hailperin', indenter, '\n', ' '),
  );
}

module.exports = { activate, indentFor };

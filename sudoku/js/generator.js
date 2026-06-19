/*
 * Sudoku puzzle engine.
 * --------------------------------------------------------------------------
 * Generates a full valid 9×9 solution, then digs out cells while a HUMAN-STYLE
 * logic solver can still finish the board using only techniques up to the
 * requested difficulty. Because the grader solves by deduction alone (never a
 * blind guess), every puzzle it accepts is automatically unique AND solvable
 * with no guessing. Difficulty is the hardest technique the puzzle forces:
 *   easy   — naked/hidden singles only
 *   medium — + locked candidates, naked/hidden pairs
 *   hard   — + naked/hidden triples, X-Wing
 * Framework-free; attaches window.Sudoku.
 */
(function () {
  "use strict";

  function mulberry32(seed) {
    let a = seed >>> 0;
    return function () {
      a |= 0; a = (a + 0x6d2b79f5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function shuffle(arr, rng) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  function canPlace(g, r, c, v) {
    for (let i = 0; i < 9; i++) if (g[r][i] === v || g[i][c] === v) return false;
    const br = r - (r % 3), bc = c - (c % 3);
    for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) if (g[br + i][bc + j] === v) return false;
    return true;
  }

  // Fill an empty grid with a random complete valid solution.
  function fillFull(rng) {
    const g = Array.from({ length: 9 }, () => new Array(9).fill(0));
    function bt(idx) {
      if (idx === 81) return true;
      const r = (idx / 9) | 0, c = idx % 9;
      for (const v of shuffle([1, 2, 3, 4, 5, 6, 7, 8, 9], rng)) {
        if (canPlace(g, r, c, v)) {
          g[r][c] = v;
          if (bt(idx + 1)) return true;
          g[r][c] = 0;
        }
      }
      return false;
    }
    bt(0);
    return g;
  }

  // ---- Bitmask helpers (bit v set means digit v is a candidate) -------------
  const ALL = 0x3fe; // bits 1..9
  function bit(v) { return 1 << v; }
  function popcount(m) { let n = 0; while (m) { m &= m - 1; n++; } return n; }
  function bitsOf(m) { const o = []; for (let v = 1; v <= 9; v++) if (m & bit(v)) o.push(v); return o; }

  // ---- Units: 9 rows, 9 cols, 9 boxes (each a list of [r,c]) ----------------
  const UNITS = (function () {
    const u = [];
    for (let r = 0; r < 9; r++) { const cells = []; for (let c = 0; c < 9; c++) cells.push([r, c]); u.push(cells); }
    for (let c = 0; c < 9; c++) { const cells = []; for (let r = 0; r < 9; r++) cells.push([r, c]); u.push(cells); }
    for (let br = 0; br < 9; br += 3) for (let bc = 0; bc < 9; bc += 3) {
      const cells = [];
      for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) cells.push([br + i, bc + j]);
      u.push(cells);
    }
    return u;
  })();

  function buildCandidates(puzzle) {
    const cand = Array.from({ length: 9 }, () => new Array(9).fill(0));
    for (let r = 0; r < 9; r++)
      for (let c = 0; c < 9; c++) {
        if (puzzle[r][c]) { cand[r][c] = bit(puzzle[r][c]); continue; }
        let m = ALL;
        for (let i = 0; i < 9; i++) { m &= ~bit(puzzle[r][i]); m &= ~bit(puzzle[i][c]); }
        const br = r - (r % 3), bc = c - (c % 3);
        for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) m &= ~bit(puzzle[br + i][bc + j]);
        cand[r][c] = m;
      }
    return cand;
  }

  function place(g, cand, r, c, v) {
    g[r][c] = v; cand[r][c] = bit(v);
    const b = bit(v);
    for (let i = 0; i < 9; i++) { if (i !== c) cand[r][i] &= ~b; if (i !== r) cand[i][c] &= ~b; }
    const br = r - (r % 3), bc = c - (c % 3);
    for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
      const rr = br + i, cc = bc + j;
      if (rr !== r || cc !== c) cand[rr][cc] &= ~b;
    }
  }

  // ---- Techniques. Each returns true on progress. Grouped by difficulty. ----

  function nakedSingle(g, cand) {
    for (let r = 0; r < 9; r++) for (let c = 0; c < 9; c++)
      if (!g[r][c] && popcount(cand[r][c]) === 1) { place(g, cand, r, c, bitsOf(cand[r][c])[0]); return true; }
    return false;
  }

  function hiddenSingle(g, cand) {
    for (const unit of UNITS)
      for (let v = 1; v <= 9; v++) {
        const b = bit(v); let spot = null, cnt = 0, placed = false;
        for (const [r, c] of unit) {
          if (g[r][c] === v) { placed = true; break; }
          if (!g[r][c] && (cand[r][c] & b)) { cnt++; spot = [r, c]; }
        }
        if (!placed && cnt === 1) { place(g, cand, spot[0], spot[1], v); return true; }
      }
    return false;
  }

  // Locked candidates: a digit confined within a box to one line (or within a
  // line to one box) is eliminated from the rest of the intersecting unit.
  function lockedCandidates(g, cand) {
    let changed = false;
    for (let v = 1; v <= 9; v++) {
      const b = bit(v);
      // Pointing: box -> row/col
      for (let br = 0; br < 9; br += 3) for (let bc = 0; bc < 9; bc += 3) {
        const rows = new Set(), cols = new Set();
        for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
          const r = br + i, c = bc + j;
          if (!g[r][c] && (cand[r][c] & b)) { rows.add(r); cols.add(c); }
        }
        if (rows.size === 1) {
          const r = rows.values().next().value;
          for (let c = 0; c < 9; c++) if (c < bc || c >= bc + 3) if (!g[r][c] && (cand[r][c] & b)) { cand[r][c] &= ~b; changed = true; }
        }
        if (cols.size === 1) {
          const c = cols.values().next().value;
          for (let r = 0; r < 9; r++) if (r < br || r >= br + 3) if (!g[r][c] && (cand[r][c] & b)) { cand[r][c] &= ~b; changed = true; }
        }
      }
      // Claiming: row/col -> box
      for (let r = 0; r < 9; r++) {
        const boxes = new Set();
        for (let c = 0; c < 9; c++) if (!g[r][c] && (cand[r][c] & b)) boxes.add(c - (c % 3));
        if (boxes.size === 1) {
          const bc = boxes.values().next().value, br = r - (r % 3);
          for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) { const rr = br + i, cc = bc + j; if (rr !== r && !g[rr][cc] && (cand[rr][cc] & b)) { cand[rr][cc] &= ~b; changed = true; } }
        }
      }
      for (let c = 0; c < 9; c++) {
        const boxes = new Set();
        for (let r = 0; r < 9; r++) if (!g[r][c] && (cand[r][c] & b)) boxes.add(r - (r % 3));
        if (boxes.size === 1) {
          const br = boxes.values().next().value, bc = c - (c % 3);
          for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) { const rr = br + i, cc = bc + j; if (cc !== c && !g[rr][cc] && (cand[rr][cc] & b)) { cand[rr][cc] &= ~b; changed = true; } }
        }
      }
    }
    return changed;
  }

  // Naked subset of size k: k cells in a unit whose candidates union to exactly
  // k digits — those digits leave every other cell in the unit.
  function nakedSubset(g, cand, k) {
    let changed = false;
    for (const unit of UNITS) {
      const open = unit.filter(([r, c]) => !g[r][c]);
      const n = open.length;
      for (let i = 0; i < n; i++) {
        for (let j = i + 1; j < n; j++) {
          if (k === 2) {
            const m = cand[open[i][0]][open[i][1]] | cand[open[j][0]][open[j][1]];
            if (popcount(m) === 2) changed = elimOutside(g, cand, unit, [open[i], open[j]], m) || changed;
          } else {
            for (let l = j + 1; l < n; l++) {
              const m = cand[open[i][0]][open[i][1]] | cand[open[j][0]][open[j][1]] | cand[open[l][0]][open[l][1]];
              if (popcount(m) === 3) changed = elimOutside(g, cand, unit, [open[i], open[j], open[l]], m) || changed;
            }
          }
        }
      }
    }
    return changed;
  }
  function elimOutside(g, cand, unit, group, mask) {
    let changed = false;
    const inGroup = new Set(group.map(([r, c]) => r * 9 + c));
    for (const [r, c] of unit) {
      if (g[r][c] || inGroup.has(r * 9 + c)) continue;
      if (cand[r][c] & mask) { cand[r][c] &= ~mask; changed = true; }
    }
    return changed;
  }

  // Hidden subset of size k: k digits that appear only within the same k cells
  // of a unit — those cells lose all other candidates.
  function hiddenSubset(g, cand, k) {
    let changed = false;
    for (const unit of UNITS) {
      const spots = {}; // digit -> list of cells
      for (let v = 1; v <= 9; v++) {
        const b = bit(v), cells = [];
        for (const [r, c] of unit) if (!g[r][c] && (cand[r][c] & b)) cells.push([r, c]);
        if (cells.length >= 2 && cells.length <= k) spots[v] = cells;
      }
      const digits = Object.keys(spots).map(Number);
      const combos = kCombos(digits, k);
      for (const combo of combos) {
        const cellSet = new Set();
        for (const v of combo) for (const [r, c] of spots[v]) cellSet.add(r * 9 + c);
        if (cellSet.size !== k) continue;
        let mask = 0; for (const v of combo) mask |= bit(v);
        for (const key of cellSet) {
          const r = (key / 9) | 0, c = key % 9;
          if (cand[r][c] & ~mask) { cand[r][c] &= mask; changed = true; }
        }
      }
    }
    return changed;
  }
  function kCombos(arr, k) {
    const out = [];
    (function rec(start, acc) {
      if (acc.length === k) { out.push(acc.slice()); return; }
      for (let i = start; i < arr.length; i++) { acc.push(arr[i]); rec(i + 1, acc); acc.pop(); }
    })(0, []);
    return out;
  }

  // X-Wing: a digit forming a rectangle across two rows/cols eliminates that
  // digit from the crossing lines.
  function xWing(g, cand) {
    let changed = false;
    for (let v = 1; v <= 9; v++) {
      const b = bit(v);
      // row-based
      const rowCols = [];
      for (let r = 0; r < 9; r++) { const cs = []; for (let c = 0; c < 9; c++) if (!g[r][c] && (cand[r][c] & b)) cs.push(c); rowCols.push(cs); }
      for (let r1 = 0; r1 < 9; r1++) {
        if (rowCols[r1].length !== 2) continue;
        for (let r2 = r1 + 1; r2 < 9; r2++) {
          if (rowCols[r2].length !== 2) continue;
          if (rowCols[r1][0] === rowCols[r2][0] && rowCols[r1][1] === rowCols[r2][1]) {
            const [c1, c2] = rowCols[r1];
            for (let r = 0; r < 9; r++) if (r !== r1 && r !== r2) {
              for (const c of [c1, c2]) if (!g[r][c] && (cand[r][c] & b)) { cand[r][c] &= ~b; changed = true; }
            }
          }
        }
      }
      // col-based
      const colRows = [];
      for (let c = 0; c < 9; c++) { const rs = []; for (let r = 0; r < 9; r++) if (!g[r][c] && (cand[r][c] & b)) rs.push(r); colRows.push(rs); }
      for (let c1 = 0; c1 < 9; c1++) {
        if (colRows[c1].length !== 2) continue;
        for (let c2 = c1 + 1; c2 < 9; c2++) {
          if (colRows[c2].length !== 2) continue;
          if (colRows[c1][0] === colRows[c2][0] && colRows[c1][1] === colRows[c2][1]) {
            const [r1, r2] = colRows[c1];
            for (let c = 0; c < 9; c++) if (c !== c1 && c !== c2) {
              for (const r of [r1, r2]) if (!g[r][c] && (cand[r][c] & b)) { cand[r][c] &= ~b; changed = true; }
            }
          }
        }
      }
    }
    return changed;
  }

  // Techniques ordered by difficulty level (1 easy, 2 medium, 3 hard).
  const TECHNIQUES = [
    { level: 1, fn: nakedSingle },
    { level: 1, fn: hiddenSingle },
    { level: 2, fn: lockedCandidates },
    { level: 2, fn: (g, cand) => nakedSubset(g, cand, 2) },
    { level: 2, fn: (g, cand) => hiddenSubset(g, cand, 2) },
    { level: 3, fn: (g, cand) => nakedSubset(g, cand, 3) },
    { level: 3, fn: (g, cand) => hiddenSubset(g, cand, 3) },
    { level: 3, fn: xWing }
  ];

  // Solve by deduction using techniques up to `maxLevel`. Returns the hardest
  // level used, or -1 if the board can't be finished within that bound.
  function gradeSolve(puzzle, maxLevel) {
    const g = puzzle.map((row) => row.slice());
    const cand = buildCandidates(g);
    // Immediate contradiction (an empty cell with no candidates)?
    for (let r = 0; r < 9; r++) for (let c = 0; c < 9; c++) if (!g[r][c] && cand[r][c] === 0) return -1;

    let used = 0;
    while (true) {
      let solved = true;
      for (let r = 0; r < 9 && solved; r++) for (let c = 0; c < 9; c++) if (!g[r][c]) { solved = false; break; }
      if (solved) return used;

      let progressed = false;
      for (const t of TECHNIQUES) {
        if (t.level > maxLevel) continue;
        if (t.fn(g, cand)) { used = Math.max(used, t.level); progressed = true; break; }
      }
      if (!progressed) return -1; // stuck within the allowed techniques
      for (let r = 0; r < 9; r++) for (let c = 0; c < 9; c++) if (!g[r][c] && cand[r][c] === 0) return -1;
    }
  }

  // Per difficulty: the hardest technique allowed, the clue floor to dig toward,
  // the minimum technique level the puzzle must REQUIRE, and a clue count at
  // which we're happy to stop searching early.
  const DIFF = {
    easy:   { maxLevel: 1, floor: 36, needLevel: 1, earlyGivens: 99 },
    medium: { maxLevel: 2, floor: 28, needLevel: 2, earlyGivens: 30 },
    hard:   { maxLevel: 3, floor: 23, needLevel: 2, earlyGivens: 25 }
  };

  // Dig one puzzle from `solution`, removing cells while it stays solvable using
  // techniques up to `maxLevel` (which also keeps it unique, since deduction
  // never branches). Returns { puzzle, givens, grade }.
  function digOne(solution, cfg, rng) {
    const puzzle = solution.map((row) => row.slice());
    let givens = 81;
    for (const idx of shuffle([...Array(81).keys()], rng)) {
      if (givens <= cfg.floor) break;
      const r = (idx / 9) | 0, c = idx % 9;
      const prev = puzzle[r][c];
      if (prev === 0) continue;
      puzzle[r][c] = 0;
      if (gradeSolve(puzzle, cfg.maxLevel) < 0) puzzle[r][c] = prev; // would need guessing -> revert
      else givens--;
    }
    return { puzzle: puzzle, givens: givens, grade: gradeSolve(puzzle, cfg.maxLevel) };
  }

  // opts: { difficulty: 'easy'|'medium'|'hard', seed }
  // Tries several full solutions and keeps the best board that genuinely
  // REQUIRES the target difficulty (so "medium" isn't a thinly-dug easy board).
  function generate(opts) {
    opts = opts || {};
    const rng = typeof opts.seed === "number" ? mulberry32(opts.seed) : Math.random;
    const difficulty = DIFF[opts.difficulty] ? opts.difficulty : "medium";
    const cfg = DIFF[difficulty];
    const ATTEMPTS = 24;

    let best = null;
    for (let a = 0; a < ATTEMPTS; a++) {
      const sol = fillFull(rng);
      const d = digOne(sol, cfg, rng);
      const meets = d.grade >= cfg.needLevel;
      // Prefer boards that meet the difficulty floor, then fewer clues, then a
      // harder hardest-technique.
      const score = (meets ? 1e6 : 0) - d.givens * 100 + d.grade;
      if (!best || score > best.score) best = { sol: sol, d: d, meets: meets, score: score };
      if (meets && d.givens <= cfg.earlyGivens) break; // good enough, stop early
    }
    const d = best.d;
    return { solution: best.sol, puzzle: d.puzzle, givens: d.givens, difficulty: difficulty, level: d.grade };
  }

  function dailySeed(date) {
    const d = date || new Date();
    return d.getUTCFullYear() * 10000 + (d.getUTCMonth() + 1) * 100 + d.getUTCDate();
  }

  window.Sudoku = window.Sudoku || {};
  window.Sudoku.generate = generate;
  window.Sudoku.dailySeed = dailySeed;
})();

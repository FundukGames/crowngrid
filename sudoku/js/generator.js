/*
 * Sudoku puzzle engine.
 * --------------------------------------------------------------------------
 * Generates a full valid 9×9 solution, then removes cells while a backtracking
 * solver confirms the puzzle still has exactly one solution. Framework-free;
 * attaches window.Sudoku.
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
    for (let i = 0; i < 9; i++) {
      if (g[r][i] === v || g[i][c] === v) return false;
    }
    const br = r - (r % 3), bc = c - (c % 3);
    for (let i = 0; i < 3; i++)
      for (let j = 0; j < 3; j++)
        if (g[br + i][bc + j] === v) return false;
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

  // Count solutions up to `limit` (for uniqueness checking).
  function countSolutions(grid, limit) {
    const g = grid.map((row) => row.slice());
    let count = 0;
    function bt() {
      if (count >= limit) return;
      let r = -1, c = -1;
      for (let i = 0; i < 81 && r < 0; i++) { if (g[(i / 9) | 0][i % 9] === 0) { r = (i / 9) | 0; c = i % 9; } }
      if (r < 0) { count++; return; }
      for (let v = 1; v <= 9; v++) {
        if (canPlace(g, r, c, v)) { g[r][c] = v; bt(); g[r][c] = 0; if (count >= limit) return; }
      }
    }
    bt();
    return count;
  }

  const TARGET = { easy: 40, medium: 32, hard: 26 };

  // opts: { difficulty: 'easy'|'medium'|'hard', seed }
  function generate(opts) {
    opts = opts || {};
    const rng = typeof opts.seed === "number" ? mulberry32(opts.seed) : Math.random;
    const target = TARGET[opts.difficulty] || TARGET.medium;

    const solution = fillFull(rng);
    const puzzle = solution.map((row) => row.slice());
    let givens = 81;

    const cells = shuffle([...Array(81).keys()], rng);
    for (const idx of cells) {
      if (givens <= target) break;
      const r = (idx / 9) | 0, c = idx % 9;
      const prev = puzzle[r][c];
      if (prev === 0) continue;
      puzzle[r][c] = 0;
      if (countSolutions(puzzle, 2) !== 1) puzzle[r][c] = prev; // keep unique
      else givens--;
    }
    return { solution: solution, puzzle: puzzle, givens: givens, difficulty: opts.difficulty || "medium" };
  }

  function dailySeed(date) {
    const d = date || new Date();
    return d.getUTCFullYear() * 10000 + (d.getUTCMonth() + 1) * 100 + d.getUTCDate();
  }

  window.Sudoku = window.Sudoku || {};
  window.Sudoku.generate = generate;
  window.Sudoku.dailySeed = dailySeed;
})();

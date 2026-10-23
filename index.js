'use strict';

/**
 * Arène des jeux — serveur (un seul fichier)
 *
 * - Comptes : inscription / connexion (e-mail + pseudo + mot de passe), sessions par jeton
 * - Stockage : PostgreSQL si la variable DATABASE_URL existe (les comptes survivent aux redéploiements),
 *              sinon un fichier JSON (effacé à chaque redéploiement sur l'offre gratuite de Render)
 * - Temps réel (Socket.IO) : salon des joueurs libres, invitations, parties
 * - Jeux : Puissance 4, Pierre-Feuille-Ciseaux, Dames, Échecs, Ludo ; contre un joueur ou l'ordinateur (niveaux 1 à 3)
 * - Le site (index.html) est servi par ce serveur, ainsi que le manifeste et le service worker de l'application installable.
 *
 * Le serveur est l'arbitre : toutes les règles sont vérifiées ici, le navigateur ne fait qu'afficher.
 */

const fs = require('fs');
const path = require('path');
const http = require('http');
const crypto = require('crypto');
const { promisify } = require('util');

const randInt = (n) => Math.floor(Math.random() * n);

/* ================================================================== */
/* Puissance 4                                                         */
/* ================================================================== */

const C4 = (() => {
/**
 * Puissance 4 : règles + ordinateur (3 niveaux).
 *
 * Plateau : 6 lignes x 7 colonnes, board[r][c], r = 0 en haut.
 * 0 = vide, 1 / 2 = pions des joueurs.
 */

const ROWS = 6;
const COLS = 7;
const DIRS = [[0, 1], [1, 0], [1, 1], [1, -1]];
const CENTER_FIRST = [3, 2, 4, 1, 5, 0, 6];
const WIN_SCORE = 1_000_000;

// Les 69 fenêtres de 4 cases alignées, calculées une seule fois.
const WINDOWS = (() => {
  const out = [];
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      for (const [dr, dc] of DIRS) {
        const er = r + dr * 3;
        const ec = c + dc * 3;
        if (er < 0 || er >= ROWS || ec < 0 || ec >= COLS) continue;
        out.push([[r, c], [r + dr, c + dc], [r + dr * 2, c + dc * 2], [er, ec]]);
      }
    }
  }
  return out;
})();

const newBoard = () => Array.from({ length: ROWS }, () => new Array(COLS).fill(0));
const copyBoard = (b) => b.map((row) => row.slice());
const validMoves = (b) => {
  const moves = [];
  for (let c = 0; c < COLS; c++) if (b[0][c] === 0) moves.push(c);
  return moves;
};
const orderedMoves = (b) => CENTER_FIRST.filter((c) => b[0][c] === 0);
const isFull = (b) => b[0].every((v) => v !== 0);

/** Pose un pion dans la colonne ; renvoie la ligne d'arrivée, ou -1 si la colonne est pleine. */
function drop(b, col, player) {
  for (let r = ROWS - 1; r >= 0; r--) {
    if (b[r][col] === 0) {
      b[r][col] = player;
      return r;
    }
  }
  return -1;
}

function countDir(b, r, c, dr, dc, p) {
  let n = 0;
  r += dr;
  c += dc;
  while (r >= 0 && r < ROWS && c >= 0 && c < COLS && b[r][c] === p) {
    n++;
    r += dr;
    c += dc;
  }
  return n;
}

/** Le pion en (r, c) fait-il partie d'un alignement de 4 ou plus ? */
function winAt(b, r, c) {
  const p = b[r][c];
  if (!p) return false;
  for (const [dr, dc] of DIRS) {
    if (1 + countDir(b, r, c, dr, dc, p) + countDir(b, r, c, -dr, -dc, p) >= 4) return true;
  }
  return false;
}

/** Les cases de l'alignement passant par (r, c), ou null. */
function lineAt(b, r, c) {
  const p = b[r][c];
  if (!p) return null;
  for (const [dr, dc] of DIRS) {
    const fwd = countDir(b, r, c, dr, dc, p);
    const back = countDir(b, r, c, -dr, -dc, p);
    if (1 + fwd + back >= 4) {
      const cells = [];
      for (let s = -back; s <= fwd; s++) cells.push([r + dr * s, c + dc * s]);
      return cells;
    }
  }
  return null;
}

/** Joueur (1 ou 2) ayant un alignement sur le plateau, sinon 0. */
function winner(b) {
  for (const w of WINDOWS) {
    const p = b[w[0][0]][w[0][1]];
    if (p && w.every(([r, c]) => b[r][c] === p)) return p;
  }
  return 0;
}

/* ------------------------------------------------------------------ */
/* Ordinateur                                                          */
/* ------------------------------------------------------------------ */

const pick = (arr, rng) => arr[Math.floor(rng() * arr.length)];

function evaluate(b, me) {
  const opp = 3 - me;
  let score = 0;
  for (let r = 0; r < ROWS; r++) {
    if (b[r][3] === me) score += 3;
    else if (b[r][3] === opp) score -= 3;
  }
  for (const w of WINDOWS) {
    let m = 0;
    let o = 0;
    for (const [r, c] of w) {
      const v = b[r][c];
      if (v === me) m++;
      else if (v === opp) o++;
    }
    if (m && o) continue;
    if (m === 3) score += 5;
    else if (m === 2) score += 2;
    else if (o === 3) score -= 6;
    else if (o === 2) score -= 2;
  }
  return score;
}

function search(b, depth, alpha, beta, maximizing, me, lr, lc) {
  if (lr >= 0 && winAt(b, lr, lc)) return (b[lr][lc] === me ? 1 : -1) * (WIN_SCORE + depth);
  const moves = orderedMoves(b);
  if (moves.length === 0) return 0;
  if (depth === 0) return evaluate(b, me);
  const player = maximizing ? me : 3 - me;
  let best = maximizing ? -Infinity : Infinity;
  for (const c of moves) {
    const r = drop(b, c, player);
    const v = search(b, depth - 1, alpha, beta, !maximizing, me, r, c);
    b[r][c] = 0;
    if (maximizing) {
      if (v > best) best = v;
      if (best > alpha) alpha = best;
    } else {
      if (v < best) best = v;
      if (best < beta) beta = best;
    }
    if (alpha >= beta) break;
  }
  return best;
}

/** Niveau 3 : anticipe plusieurs coups (minimax avec élagage alpha-bêta). */
function minimaxMove(b, me, depth, rng) {
  let best = -Infinity;
  let bestMoves = [];
  for (const c of orderedMoves(b)) {
    const r = drop(b, c, me);
    const v = search(b, depth - 1, -Infinity, Infinity, false, me, r, c);
    b[r][c] = 0;
    if (v > best) {
      best = v;
      bestMoves = [c];
    } else if (v === best) {
      bestMoves.push(c);
    }
  }
  return pick(bestMoves, rng);
}

/** Niveau 2 : gagne si possible, bloque la plupart du temps, évite d'offrir une victoire. */
function heuristicMove(b, me, rng) {
  const opp = 3 - me;
  const moves = validMoves(b);
  const wouldWin = (c, p) => {
    const r = drop(b, c, p);
    const w = winAt(b, r, c);
    b[r][c] = 0;
    return w;
  };
  for (const c of moves) if (wouldWin(c, me)) return c;
  if (rng() < 0.8) for (const c of moves) if (wouldWin(c, opp)) return c;

  const safe = moves.filter((c) => {
    const r = drop(b, c, me);
    let ok = true;
    if (r > 0) {
      const r2 = drop(b, c, opp);
      if (winAt(b, r2, c)) ok = false;
      b[r2][c] = 0;
    }
    b[r][c] = 0;
    return ok;
  });
  const pool = safe.length ? safe : moves;
  const weights = pool.map((c) => 4 - Math.abs(3 - c)); // colonnes centrales favorisées
  let roll = rng() * weights.reduce((a, b2) => a + b2, 0);
  for (let i = 0; i < pool.length; i++) {
    roll -= weights[i];
    if (roll < 0) return pool[i];
  }
  return pool[pool.length - 1];
}

/**
 * Choisit la colonne jouée par l'ordinateur.
 * level 1 : au hasard · level 2 : tactique de base · level 3 : minimax profondeur 6
 */
function cpuMove(board, level, me, rng = Math.random) {
  const b = copyBoard(board);
  const moves = validMoves(b);
  if (moves.length === 0) return -1;
  if (level <= 1) return pick(moves, rng);
  if (level === 2) return heuristicMove(b, me, rng);
  return minimaxMove(b, me, 6, rng);
}

return {
  ROWS,
  COLS,
  newBoard,
  copyBoard,
  validMoves,
  isFull,
  drop,
  winAt,
  lineAt,
  winner,
  cpuMove,
};
})();

/* ================================================================== */
/* Pierre-Feuille-Ciseaux                                              */
/* ================================================================== */

const RPS = (() => {
/**
 * Pierre-Feuille-Ciseaux : règles + ordinateur (3 niveaux).
 *
 * Règles : on joue en plusieurs manches, le premier à 2 manches gagnées l'emporte.
 * En cas d'égalité, la manche est rejouée et ne compte pas.
 */

const MOVES = ['pierre', 'feuille', 'ciseaux'];
const TARGET = 2;

// BEATS[a] = ce que a bat
const BEATS = { pierre: 'ciseaux', feuille: 'pierre', ciseaux: 'feuille' };
// COUNTER[a] = le coup qui bat a
const COUNTER = { pierre: 'feuille', feuille: 'ciseaux', ciseaux: 'pierre' };

/** 0 si a gagne, 1 si b gagne, 'tie' en cas d'égalité. */
function outcome(a, b) {
  if (a === b) return 'tie';
  return BEATS[a] === b ? 0 : 1;
}

const pick = (arr, rng) => arr[Math.floor(rng() * arr.length)];

function mostFrequent(moves, rng) {
  const counts = { pierre: 0, feuille: 0, ciseaux: 0 };
  for (const m of moves) counts[m]++;
  const max = Math.max(...Object.values(counts));
  return pick(MOVES.filter((m) => counts[m] === max), rng);
}

/** Parmi les coups qui ont suivi `matches`, renvoie le plus fréquent s'il se détache nettement. */
function dominantNext(history, matches) {
  const counts = { pierre: 0, feuille: 0, ciseaux: 0 };
  let total = 0;
  for (let i = 0; i < history.length - 1; i++) {
    if (matches(history[i])) {
      counts[history[i + 1].h]++;
      total++;
    }
  }
  if (total < 2) return null;
  const sorted = MOVES.slice().sort((x, y) => counts[y] - counts[x]);
  return counts[sorted[0]] > counts[sorted[1]] ? sorted[0] : null;
}

/**
 * history : les manches précédentes de CE joueur contre l'ordinateur,
 * [{ h: coup du joueur, c: coup de l'ordinateur, r: 'w' | 'l' | 't' (du point de vue du joueur) }, ...]
 * L'ordinateur choisit toujours AVANT de connaître le coup en cours : il ne triche pas.
 *
 * level 1 : au hasard
 * level 2 : repère le coup préféré récent du joueur et tente de le contrer (une fois sur deux et demie)
 * level 3 : repère les enchaînements (ce que le joueur joue après tel coup / tel résultat), contre dans ~85 % des cas
 */
function cpuChoice(level, history, rng = Math.random) {
  if (level <= 1 || history.length === 0) return pick(MOVES, rng);

  if (level === 2) {
    const recent = history.slice(-12);
    if (recent.length < 3) return pick(MOVES, rng);
    const predicted = mostFrequent(recent.map((x) => x.h), rng);
    return rng() < 0.6 ? COUNTER[predicted] : pick(MOVES, rng);
  }

  const last = history[history.length - 1];
  let predicted = dominantNext(history, (x) => x.h === last.h && x.r === last.r);
  if (!predicted) predicted = dominantNext(history, (x) => x.h === last.h);
  if (!predicted && history.length >= 4) predicted = mostFrequent(history.slice(-15).map((x) => x.h), rng);
  if (!predicted) return pick(MOVES, rng);
  return rng() < 0.85 ? COUNTER[predicted] : pick(MOVES, rng);
}

return { MOVES, TARGET, outcome, cpuChoice, COUNTER };
})();
/* ================================================================== */
/* Échecs : règles complètes (roque, prise en passant, promotion, mat, */
/* pat, 50 coups, triple répétition, matériel insuffisant)             */
/* ================================================================== */

const Chess = (() => {
  const P = 1, N = 2, B = 3, R = 4, Q = 5, K = 6;
  const KN = [[-2, -1], [-2, 1], [-1, -2], [-1, 2], [1, -2], [1, 2], [2, -1], [2, 1]];
  const KG = [[-1, -1], [-1, 0], [-1, 1], [0, -1], [0, 1], [1, -1], [1, 0], [1, 1]];
  const BD = [[-1, -1], [-1, 1], [1, -1], [1, 1]];
  const RD = [[-1, 0], [1, 0], [0, -1], [0, 1]];
  const VALUE = [0, 100, 320, 330, 500, 900, 0];
  const MATE = 100000;

  const PST = [
    null,
    [0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 10, 10, 20, 30, 30, 20, 10, 10, 5, 5, 10, 25, 25, 10, 5, 5, 0, 0, 0, 20, 20, 0, 0, 0, 5, -5, -10, 0, 0, -10, -5, 5, 5, 10, 10, -20, -20, 10, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0],
    [-50, -40, -30, -30, -30, -30, -40, -50, -40, -20, 0, 0, 0, 0, -20, -40, -30, 0, 10, 15, 15, 10, 0, -30, -30, 5, 15, 20, 20, 15, 5, -30, -30, 0, 15, 20, 20, 15, 0, -30, -30, 5, 10, 15, 15, 10, 5, -30, -40, -20, 0, 5, 5, 0, -20, -40, -50, -40, -30, -30, -30, -30, -40, -50],
    [-20, -10, -10, -10, -10, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 10, 10, 5, 0, -10, -10, 5, 5, 10, 10, 5, 5, -10, -10, 0, 10, 10, 10, 10, 0, -10, -10, 10, 10, 10, 10, 10, 10, -10, -10, 5, 0, 0, 0, 0, 5, -10, -20, -10, -10, -10, -10, -10, -10, -20],
    [0, 0, 0, 0, 0, 0, 0, 0, 5, 10, 10, 10, 10, 10, 10, 5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 5, 5, 0, 0, 0],
    [-20, -10, -10, -5, -5, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 5, 5, 5, 0, -10, -5, 0, 5, 5, 5, 5, 0, -5, 0, 0, 5, 5, 5, 5, 0, -5, -10, 5, 5, 5, 5, 5, 0, -10, -10, 0, 5, 0, 0, 0, 0, -10, -20, -10, -10, -5, -5, -10, -10, -20],
    [-30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -20, -30, -30, -40, -40, -30, -30, -20, -10, -20, -20, -20, -20, -20, -20, -10, 20, 20, 0, 0, 0, 0, 20, 20, 20, 30, 10, 0, 0, 10, 30, 20],
  ];
  // Roi en fin de partie : il doit se centraliser.
  const KING_END = [-50, -40, -30, -20, -20, -30, -40, -50, -30, -20, -10, 0, 0, -10, -20, -30, -30, -10, 20, 30, 30, 20, -10, -30, -30, -10, 30, 40, 40, 30, -10, -30, -30, -10, 30, 40, 40, 30, -10, -30, -30, -10, 20, 30, 30, 20, -10, -30, -30, -30, 0, 0, 0, 0, -30, -30, -50, -30, -30, -30, -30, -30, -30, -50];

  function fromFEN(fen) {
    const [pl, stm, cas, ep, half] = fen.trim().split(/\s+/);
    const b = new Array(64).fill(0);
    const map = { p: 1, n: 2, b: 3, r: 4, q: 5, k: 6 };
    let i = 0;
    for (const ch of pl) {
      if (ch === '/') continue;
      if (/\d/.test(ch)) { i += Number(ch); continue; }
      const low = ch.toLowerCase();
      b[i++] = (ch === low ? -1 : 1) * map[low];
    }
    let castle = 0;
    if (cas.includes('K')) castle |= 1;
    if (cas.includes('Q')) castle |= 2;
    if (cas.includes('k')) castle |= 4;
    if (cas.includes('q')) castle |= 8;
    const epSq = ep && ep !== '-' ? (8 - Number(ep[1])) * 8 + (ep.charCodeAt(0) - 97) : -1;
    return { b, side: stm === 'w' ? 1 : -1, castle, ep: epSq, half: Number(half) || 0, ks: [b.indexOf(K), b.indexOf(-K)] };
  }
  const startPos = () => fromFEN('rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1');
  const kingOf = (pos, side) => pos.ks[side === 1 ? 0 : 1];

  /** La case sq est-elle attaquée par les pièces du camp `by` (1 ou -1) ? */
  function attacked(b, sq, by) {
    const r = sq >> 3, c = sq & 7;
    const pr = r + by;
    if (pr >= 0 && pr < 8) {
      if (c > 0 && b[pr * 8 + c - 1] === by * P) return true;
      if (c < 7 && b[pr * 8 + c + 1] === by * P) return true;
    }
    for (let k = 0; k < 8; k++) {
      let rr = r + KN[k][0], cc = c + KN[k][1];
      if (rr >= 0 && rr < 8 && cc >= 0 && cc < 8 && b[rr * 8 + cc] === by * N) return true;
      rr = r + KG[k][0]; cc = c + KG[k][1];
      if (rr >= 0 && rr < 8 && cc >= 0 && cc < 8 && b[rr * 8 + cc] === by * K) return true;
    }
    for (let k = 0; k < 4; k++) {
      let rr = r + BD[k][0], cc = c + BD[k][1];
      while (rr >= 0 && rr < 8 && cc >= 0 && cc < 8) {
        const v = b[rr * 8 + cc];
        if (v !== 0) { if (v === by * B || v === by * Q) return true; break; }
        rr += BD[k][0]; cc += BD[k][1];
      }
      rr = r + RD[k][0]; cc = c + RD[k][1];
      while (rr >= 0 && rr < 8 && cc >= 0 && cc < 8) {
        const v = b[rr * 8 + cc];
        if (v !== 0) { if (v === by * R || v === by * Q) return true; break; }
        rr += RD[k][0]; cc += RD[k][1];
      }
    }
    return false;
  }

  function pseudo(pos, capsOnly) {
    const { b, side, castle, ep } = pos;
    const out = [];
    for (let sq = 0; sq < 64; sq++) {
      const v = b[sq];
      if (v * side <= 0) continue;
      const t = Math.abs(v), r = sq >> 3, c = sq & 7;
      if (t === P) {
        const dir = side === 1 ? -1 : 1, startR = side === 1 ? 6 : 1, lastR = side === 1 ? 0 : 7;
        const r1 = r + dir;
        if (r1 < 0 || r1 > 7) continue;
        if (!capsOnly || r1 === lastR) {
          if (b[r1 * 8 + c] === 0) {
            if (r1 === lastR) for (const pr of [Q, R, B, N]) out.push({ from: sq, to: r1 * 8 + c, promo: pr });
            else if (!capsOnly) {
              out.push({ from: sq, to: r1 * 8 + c });
              if (r === startR && b[(r + 2 * dir) * 8 + c] === 0) out.push({ from: sq, to: (r + 2 * dir) * 8 + c, flag: 'dbl' });
            }
          }
        }
        for (let dc = -1; dc <= 1; dc += 2) {
          const cc = c + dc;
          if (cc < 0 || cc > 7) continue;
          const to = r1 * 8 + cc, tv = b[to];
          if (tv * side < 0) {
            if (r1 === lastR) for (const pr of [Q, R, B, N]) out.push({ from: sq, to, promo: pr });
            else out.push({ from: sq, to });
          } else if (to === ep && tv === 0) out.push({ from: sq, to, flag: 'ep' });
        }
      } else if (t === N || t === K) {
        const dirs = t === N ? KN : KG;
        for (let k = 0; k < 8; k++) {
          const rr = r + dirs[k][0], cc = c + dirs[k][1];
          if (rr < 0 || rr > 7 || cc < 0 || cc > 7) continue;
          const tv = b[rr * 8 + cc];
          if (tv * side <= 0 && (!capsOnly || tv !== 0)) out.push({ from: sq, to: rr * 8 + cc });
        }
        if (t === K && !capsOnly) {
          const home = side === 1 ? 60 : 4;
          if (sq === home) {
            const kBit = side === 1 ? 1 : 4, qBit = side === 1 ? 2 : 8;
            if ((castle & kBit) && b[home + 1] === 0 && b[home + 2] === 0 && b[home + 3] === side * R &&
                !attacked(b, home, -side) && !attacked(b, home + 1, -side)) out.push({ from: sq, to: home + 2, flag: 'castleK' });
            if ((castle & qBit) && b[home - 1] === 0 && b[home - 2] === 0 && b[home - 3] === 0 && b[home - 4] === side * R &&
                !attacked(b, home, -side) && !attacked(b, home - 1, -side)) out.push({ from: sq, to: home - 2, flag: 'castleQ' });
          }
        }
      } else {
        const dirs = t === B ? BD : t === R ? RD : null;
        const lists = dirs ? [dirs] : [BD, RD];
        for (const list of lists) {
          for (let k = 0; k < 4; k++) {
            let rr = r + list[k][0], cc = c + list[k][1];
            while (rr >= 0 && rr < 8 && cc >= 0 && cc < 8) {
              const tv = b[rr * 8 + cc];
              if (tv * side > 0) break;
              if (!capsOnly || tv !== 0) out.push({ from: sq, to: rr * 8 + cc });
              if (tv !== 0) break;
              rr += list[k][0]; cc += list[k][1];
            }
          }
        }
      }
    }
    return out;
  }

  function make(pos, m) {
    const b = pos.b.slice();
    const side = pos.side;
    const p = b[m.from];
    let cap = b[m.to];
    let castle = pos.castle, ep = -1, half = pos.half + 1;
    const ks = pos.ks.slice();
    b[m.from] = 0;
    if (Math.abs(p) === P) {
      half = 0;
      if (m.flag === 'ep') { b[(m.from >> 3) * 8 + (m.to & 7)] = 0; cap = -side; }
      if (m.flag === 'dbl') ep = (m.from + m.to) >> 1;
    }
    if (cap !== 0) half = 0;
    b[m.to] = m.promo ? m.promo * side : p;
    if (m.flag === 'castleK') { b[m.to - 1] = b[m.to + 1]; b[m.to + 1] = 0; }
    if (m.flag === 'castleQ') { b[m.to + 1] = b[m.to - 2]; b[m.to - 2] = 0; }
    if (Math.abs(p) === K) { castle &= side === 1 ? ~3 : ~12; ks[side === 1 ? 0 : 1] = m.to; }
    const touch = (sq) => {
      if (sq === 56) castle &= ~2; else if (sq === 63) castle &= ~1; else if (sq === 0) castle &= ~8; else if (sq === 7) castle &= ~4;
    };
    touch(m.from); touch(m.to);
    return { b, side: -side, castle, ep, half, ks };
  }

  const inCheck = (pos) => attacked(pos.b, kingOf(pos, pos.side), -pos.side);

  function legal(pos) {
    const out = [];
    const ksq = pos.side === 1 ? 0 : 1;
    for (const m of pseudo(pos, false)) {
      const np = make(pos, m);
      if (!attacked(np.b, np.ks[ksq], np.side)) out.push(m);
    }
    return out;
  }

  function perft(pos, depth) {
    if (depth === 0) return 1;
    const moves = legal(pos);
    if (depth === 1) return moves.length;
    let n = 0;
    for (const m of moves) n += perft(make(pos, m), depth - 1);
    return n;
  }

  /* ---------------- Évaluation et recherche ---------------- */

  function evaluate(pos) {
    const b = pos.b;
    let score = 0, minors = 0, queens = 0;
    for (let sq = 0; sq < 64; sq++) {
      const v = b[sq];
      if (!v) continue;
      const t = Math.abs(v);
      if (t === Q) queens++;
      if (t === N || t === B || t === R) minors++;
    }
    const endgame = queens === 0 || minors <= 3;
    for (let sq = 0; sq < 64; sq++) {
      const v = b[sq];
      if (!v) continue;
      const t = Math.abs(v);
      const white = v > 0;
      const idx = white ? sq : sq ^ 56;
      const table = t === K && endgame ? KING_END : PST[t];
      const s = VALUE[t] + table[idx];
      score += white ? s : -s;
    }
    return score * pos.side;
  }

  const isCapture = (pos, m) => pos.b[m.to] !== 0 || m.flag === 'ep';
  function orderMoves(pos, moves) {
    const b = pos.b;
    for (const m of moves) {
      let s = 0;
      const victim = Math.abs(b[m.to]);
      if (victim) s += 10 * VALUE[victim] - VALUE[Math.abs(b[m.from])];
      else if (m.flag === 'ep') s += 900;
      if (m.promo) s += VALUE[m.promo];
      m.s = s;
    }
    moves.sort((x, y) => y.s - x.s);
    return moves;
  }

  class Timeout extends Error {}

  function search(pos, depth, alpha, beta, ply, ctx) {
    if ((++ctx.nodes & 1023) === 0 && Date.now() > ctx.deadline) throw new Timeout();
    const moves = legal(pos);
    if (moves.length === 0) return inCheck(pos) ? -MATE + ply : 0;
    if (pos.half >= 100) return 0;
    if (depth <= 0) return ctx.quiesce ? qsearch(pos, alpha, beta, 0, ctx) : evaluate(pos);
    orderMoves(pos, moves);
    for (const m of moves) {
      const score = -search(make(pos, m), depth - 1, -beta, -alpha, ply + 1, ctx);
      if (score >= beta) return beta;
      if (score > alpha) alpha = score;
    }
    return alpha;
  }

  function qsearch(pos, alpha, beta, qd, ctx) {
    if ((++ctx.nodes & 1023) === 0 && Date.now() > ctx.deadline) throw new Timeout();
    const stand = evaluate(pos);
    if (stand >= beta) return beta;
    if (stand > alpha) alpha = stand;
    if (qd >= 4) return alpha;
    const ksq = pos.side === 1 ? 0 : 1;
    const caps = orderMoves(pos, pseudo(pos, true));
    for (const m of caps) {
      const np = make(pos, m);
      if (attacked(np.b, np.ks[ksq], np.side)) continue;
      const score = -qsearch(np, -beta, -alpha, qd + 1, ctx);
      if (score >= beta) return beta;
      if (score > alpha) alpha = score;
    }
    return alpha;
  }

  /** Choisit un coup légal. level 1 : hasard · 2 : 2 coups d'avance · 3 : jusqu'à ~1 s de réflexion + captures. */
  function bestMove(pos, level, rng = Math.random) {
    const moves = legal(pos);
    if (!moves.length) return null;
    if (level <= 1) return moves[Math.floor(rng() * moves.length)];
    const ctx = { nodes: 0, deadline: Date.now() + (level === 2 ? 400 : 700), quiesce: level >= 3 };
    orderMoves(pos, moves);
    let scored = moves.map((m) => ({ m, s: 0 }));
    const maxDepth = level === 2 ? 2 : 8;
    for (let d = 1; d <= maxDepth; d++) {
      try {
        const next = [];
        let alpha = -Infinity;
        for (const { m } of scored) {
          const s = -search(make(pos, m), d - 1, -Infinity, level === 2 ? Infinity : -alpha, 1, ctx);
          next.push({ m, s });
          if (s > alpha) alpha = s;
        }
        next.sort((x, y) => y.s - x.s);
        scored = next;
        if (Math.abs(scored[0].s) > MATE - 100) break;
      } catch (e) {
        if (e instanceof Timeout) break;
        throw e;
      }
    }
    if (level === 2) {
      const top = scored[0].s;
      const near = scored.filter((x) => x.s >= top - 15);
      return near[Math.floor(rng() * near.length)].m;
    }
    return scored[0].m;
  }

  /* ---------------- Fin de partie ---------------- */

  const posKey = (pos) => `${pos.b.join(',')}|${pos.side}|${pos.castle}|${pos.ep}`;
  function insufficient(pos) {
    const minors = [];
    for (const v of pos.b) {
      const t = Math.abs(v);
      if (t === 0 || t === K) continue;
      if (t === P || t === R || t === Q) return false;
      minors.push(t);
    }
    return minors.length <= 1;
  }

  /* ---------------- Interface avec le serveur ---------------- */

  const rc = (sq) => [sq >> 3, sq & 7];
  const sqOf = (a) => (Array.isArray(a) && a.length === 2 && Number.isInteger(a[0]) && Number.isInteger(a[1]) && a[0] >= 0 && a[0] < 8 && a[1] >= 0 && a[1] < 8 ? a[0] * 8 + a[1] : -1);

  function init(starter) {
    const pos = startPos();
    return { pos, starter, turn: starter, hist: [posKey(pos)], last: null, result: null, legal: legal(pos) };
  }

  function play(state, idx, p) {
    if (state.result) return 'La partie est terminée.';
    if (state.turn !== idx) return "Ce n'est pas ton tour.";
    const from = sqOf(p.from), to = sqOf(p.to);
    if (from < 0 || to < 0) return 'Coup invalide.';
    const cands = state.legal.filter((m) => m.from === from && m.to === to);
    if (!cands.length) return 'Coup illégal.';
    let m = cands[0];
    if (cands.length > 1) {
      const want = { q: Q, r: R, b: B, n: N }[p.promo] || Q;
      m = cands.find((x) => x.promo === want) || cands.find((x) => x.promo === Q);
    }
    const mover = state.turn;
    state.pos = make(state.pos, m);
    state.turn = 1 - state.turn;
    state.last = { from, to };
    state.hist.push(posKey(state.pos));
    state.legal = legal(state.pos);
    if (state.legal.length === 0) {
      state.result = inCheck(state.pos) ? { winner: mover, reason: 'checkmate' } : { winner: 'draw', reason: 'stalemate' };
    } else if (state.pos.half >= 100) {
      state.result = { winner: 'draw', reason: 'fifty' };
    } else if (state.hist.filter((k) => k === state.hist[state.hist.length - 1]).length >= 3) {
      state.result = { winner: 'draw', reason: 'repetition' };
    } else if (insufficient(state.pos)) {
      state.result = { winner: 'draw', reason: 'material' };
    }
    return null;
  }

  function view(state) {
    const seen = new Set();
    const legalList = [];
    if (!state.result) {
      for (const m of state.legal) {
        const key = m.from * 64 + m.to;
        if (seen.has(key)) continue;
        seen.add(key);
        legalList.push([m.from, m.to, m.promo ? 1 : 0]);
      }
    }
    return {
      board: state.pos.b,
      turn: state.turn,
      starter: state.starter,
      check: !state.result && inCheck(state.pos) ? kingOf(state.pos, state.pos.side) : -1,
      last: state.last,
      legal: legalList,
    };
  }

  function cpu(state, level, rng = Math.random) {
    const m = bestMove(state.pos, level, rng);
    const to = rc(m.to);
    const out = { from: rc(m.from), to };
    if (m.promo) out.promo = 'qrbn'[[Q, R, B, N].indexOf(m.promo)];
    return out;
  }

  function randomPayload(state) {
    return cpu(state, 1);
  }

  return { fromFEN, startPos, legal, make, perft, inCheck, evaluate, bestMove, init, play, view, cpu, randomPayload, isCapture };
})();
/* ================================================================== */
/* Dames internationales (10x10)                                       */
/* - le pion avance en diagonale, prend en avant et en arrière          */
/* - la prise est obligatoire, et il faut prendre le maximum de pièces  */
/* - la dame se déplace et prend de loin ("dame volante")               */
/* - une pièce prise est retirée à la fin de la rafle, jamais deux fois */
/* ================================================================== */

const Dames = (() => {
  const DIRS = [[-1, -1], [-1, 1], [1, -1], [1, 1]];
  const MAN_VALUE = 100, KING_VALUE = 320;
  const MATE = 100000;

  // Plateau : tableau de 100 cases (r*10+c). >0 : blancs (1 pion, 2 dame), <0 : noirs. Blancs en bas, ils jouent en premier.
  function initialBoard() {
    const b = new Array(100).fill(0);
    for (let r = 0; r < 10; r++) {
      for (let c = 0; c < 10; c++) {
        if ((r + c) % 2 !== 1) continue;
        if (r <= 3) b[r * 10 + c] = -1;
        else if (r >= 6) b[r * 10 + c] = 1;
      }
    }
    return b;
  }

  function dfs(b, side, king, r, c, from, caps, path, out) {
    let found = false;
    for (let d = 0; d < 4; d++) {
      const dr = DIRS[d][0], dc = DIRS[d][1];
      if (!king) {
        const r1 = r + dr, c1 = c + dc, r2 = r + 2 * dr, c2 = c + 2 * dc;
        if (r2 < 0 || r2 > 9 || c2 < 0 || c2 > 9) continue;
        const i1 = r1 * 10 + c1;
        if (b[i1] * side >= 0) continue;
        if (caps.includes(i1)) continue;
        if (b[r2 * 10 + c2] !== 0) continue;
        found = true;
        caps.push(i1); path.push(r2 * 10 + c2);
        dfs(b, side, king, r2, c2, from, caps, path, out);
        caps.pop(); path.pop();
      } else {
        let rr = r + dr, cc = c + dc;
        while (rr >= 0 && rr < 10 && cc >= 0 && cc < 10 && b[rr * 10 + cc] === 0) { rr += dr; cc += dc; }
        if (rr < 0 || rr > 9 || cc < 0 || cc > 9) continue;
        const ei = rr * 10 + cc;
        if (b[ei] * side >= 0 || caps.includes(ei)) continue;
        let lr = rr + dr, lc = cc + dc;
        while (lr >= 0 && lr < 10 && lc >= 0 && lc < 10 && b[lr * 10 + lc] === 0) {
          found = true;
          caps.push(ei); path.push(lr * 10 + lc);
          dfs(b, side, king, lr, lc, from, caps, path, out);
          caps.pop(); path.pop();
          lr += dr; lc += dc;
        }
      }
    }
    if (!found && caps.length) out.push({ from, to: path[path.length - 1], caps: caps.slice(), path: path.slice() });
  }

  function genMoves(b, side) {
    // 1) rafles : obligatoires, et on ne garde que les plus longues
    let caps = [];
    for (let i = 0; i < 100; i++) {
      const p = b[i];
      if (p * side <= 0) continue;
      const saved = b[i];
      b[i] = 0;
      dfs(b, side, Math.abs(p) === 2, (i / 10) | 0, i % 10, i, [], [], caps);
      b[i] = saved;
    }
    if (caps.length) {
      let max = 0;
      for (const m of caps) if (m.caps.length > max) max = m.caps.length;
      return caps.filter((m) => m.caps.length === max);
    }
    // 2) déplacements simples
    const out = [];
    for (let i = 0; i < 100; i++) {
      const p = b[i];
      if (p * side <= 0) continue;
      const r = (i / 10) | 0, c = i % 10;
      if (Math.abs(p) === 1) {
        const dr = side === 1 ? -1 : 1;
        for (const dc of [-1, 1]) {
          const rr = r + dr, cc = c + dc;
          if (rr >= 0 && rr < 10 && cc >= 0 && cc < 10 && b[rr * 10 + cc] === 0) out.push({ from: i, to: rr * 10 + cc, caps: [], path: [rr * 10 + cc] });
        }
      } else {
        for (let d = 0; d < 4; d++) {
          let rr = r + DIRS[d][0], cc = c + DIRS[d][1];
          while (rr >= 0 && rr < 10 && cc >= 0 && cc < 10 && b[rr * 10 + cc] === 0) {
            out.push({ from: i, to: rr * 10 + cc, caps: [], path: [rr * 10 + cc] });
            rr += DIRS[d][0]; cc += DIRS[d][1];
          }
        }
      }
    }
    return out;
  }

  function apply(b, m, side) {
    const p = b[m.from];
    b[m.from] = 0;
    for (const c of m.caps) b[c] = 0;
    const r = (m.to / 10) | 0;
    b[m.to] = Math.abs(p) === 1 && ((side === 1 && r === 0) || (side === -1 && r === 9)) ? 2 * side : p;
  }

  /* ---------------- Ordinateur ---------------- */

  function evaluate(b, side) {
    let s = 0;
    for (let i = 0; i < 100; i++) {
      const p = b[i];
      if (!p) continue;
      const sg = p > 0 ? 1 : -1, r = (i / 10) | 0, c = i % 10;
      let v;
      if (Math.abs(p) === 2) v = KING_VALUE + (c >= 2 && c <= 7 && r >= 2 && r <= 7 ? 6 : 0);
      else {
        const adv = sg === 1 ? 9 - r : r;
        v = MAN_VALUE + adv * 3 + (c >= 3 && c <= 6 ? 3 : 0) + ((sg === 1 && r === 9) || (sg === -1 && r === 0) ? 4 : 0);
      }
      s += sg * v;
    }
    return s * side;
  }

  class Timeout extends Error {}

  function negamax(b, side, depth, alpha, beta, ply, ctx) {
    if ((++ctx.nodes & 511) === 0 && Date.now() > ctx.deadline) throw new Timeout();
    const moves = genMoves(b, side);
    if (!moves.length) return -MATE + ply;
    if (depth <= 0) return evaluate(b, side);
    moves.sort((x, y) => y.caps.length - x.caps.length);
    for (const m of moves) {
      const nb = b.slice();
      apply(nb, m, side);
      const score = -negamax(nb, -side, depth - 1, -beta, -alpha, ply + 1, ctx);
      if (score >= beta) return beta;
      if (score > alpha) alpha = score;
    }
    return alpha;
  }

  function bestMove(b, side, level, rng = Math.random) {
    const moves = genMoves(b, side);
    if (!moves.length) return null;
    if (level <= 1 || moves.length === 1) return moves[Math.floor(rng() * moves.length)];
    const ctx = { nodes: 0, deadline: Date.now() + (level === 2 ? 250 : 800) };
    let scored = moves.map((m) => ({ m, s: 0 }));
    const maxDepth = level === 2 ? 2 : 12;
    for (let d = 1; d <= maxDepth; d++) {
      try {
        const next = [];
        let alpha = -Infinity;
        for (const { m } of scored) {
          const nb = b.slice();
          apply(nb, m, side);
          const s = -negamax(nb, -side, d - 1, -Infinity, level === 2 ? Infinity : -alpha, 1, ctx);
          next.push({ m, s });
          if (s > alpha) alpha = s;
        }
        next.sort((x, y) => y.s - x.s);
        scored = next;
        if (Math.abs(scored[0].s) > MATE - 100) break;
      } catch (e) {
        if (e instanceof Timeout) break;
        throw e;
      }
    }
    if (level === 2) {
      const near = scored.filter((x) => x.s >= scored[0].s - 10);
      return near[Math.floor(rng() * near.length)].m;
    }
    return scored[0].m;
  }

  /* ---------------- Interface avec le serveur ---------------- */

  const rc = (i) => [(i / 10) | 0, i % 10];
  const idxOf = (a) => (Array.isArray(a) && a.length === 2 && Number.isInteger(a[0]) && Number.isInteger(a[1]) && a[0] >= 0 && a[0] < 10 && a[1] >= 0 && a[1] < 10 ? a[0] * 10 + a[1] : -1);
  const sideOf = (state, idx) => (idx === state.starter ? 1 : -1);

  function init(starter) {
    const board = initialBoard();
    return { board, starter, turn: starter, last: null, quiet: 0, result: null, legal: genMoves(board, 1) };
  }

  function play(state, idx, p) {
    if (state.result) return 'La partie est terminée.';
    if (state.turn !== idx) return "Ce n'est pas ton tour.";
    const from = idxOf(p.from), to = idxOf(p.to);
    if (from < 0 || to < 0) return 'Coup invalide.';
    const m = state.legal.find((x) => x.from === from && x.to === to);
    if (!m) return state.legal.some((x) => x.caps.length) ? 'Prise obligatoire (et la plus longue).' : 'Coup illégal.';
    const side = sideOf(state, idx);
    const wasKing = Math.abs(state.board[from]) === 2;
    apply(state.board, m, side);
    state.last = { from, to, caps: m.caps };
    state.quiet = m.caps.length || !wasKing ? 0 : state.quiet + 1;
    state.turn = 1 - state.turn;
    state.legal = genMoves(state.board, -side);
    if (!state.legal.length) state.result = { winner: idx, reason: 'win' };
    else if (state.quiet >= 50) state.result = { winner: 'draw', reason: 'fifty' };
    return null;
  }

  function view(state) {
    return {
      board: state.board,
      turn: state.turn,
      starter: state.starter,
      last: state.last,
      mustCapture: !state.result && state.legal.some((m) => m.caps.length > 0),
      legal: state.result ? [] : state.legal.map((m) => [m.from, m.to]),
    };
  }

  function cpu(state, level, rng = Math.random) {
    const m = bestMove(state.board, sideOf(state, state.turn), level, rng);
    return { from: rc(m.from), to: rc(m.to) };
  }

  return { initialBoard, genMoves, apply, evaluate, bestMove, init, play, view, cpu, randomPayload: (s) => cpu(s, 1) };
})();
/* ================================================================== */
/* Ludo à 2 joueurs (4 pions chacun)                                   */
/*  - il faut un 6 pour sortir un pion de l'écurie                      */
/*  - un 6, une capture ou l'arrivée d'un pion à la maison font rejouer */
/*  - on capture un pion adverse en tombant sur sa case, sauf sur une   */
/*    case étoile (départs et cases sûres) ; il retourne à l'écurie     */
/*  - il faut le nombre exact pour entrer à la maison                   */
/* ================================================================== */

const Ludo = (() => {
  const START = [0, 26]; // case de départ de chaque joueur sur la piste de 52 cases (opposées)
  const SAFE = new Set([8, 13, 21, 26, 34, 39, 47, 0]);
  const HOME = 56; // -1 : écurie · 0..50 : piste · 51..55 : couloir final · 56 : à la maison
  const abs = (i, rel) => (START[i] + rel) % 52;

  function init(starter) {
    return {
      starter,
      turn: starter,
      pawns: [[-1, -1, -1, -1], [-1, -1, -1, -1]],
      dice: null, // valeur lancée en attente du choix d'un pion
      lastRoll: null, // { by, v, note }
      lastMove: null,
      result: null,
    };
  }

  /** Pions que le joueur i peut jouer avec la valeur v. */
  function movable(state, i, v) {
    const out = [];
    state.pawns[i].forEach((p, k) => {
      if (p === HOME) return;
      if (p === -1) { if (v === 6) out.push(k); return; }
      if (p + v <= HOME) out.push(k);
    });
    return out;
  }

  function captureAt(state, i, rel) {
    if (rel < 0 || rel > 50) return [];
    const a = abs(i, rel);
    if (SAFE.has(a)) return [];
    const o = 1 - i, hit = [];
    state.pawns[o].forEach((q, k) => { if (q >= 0 && q <= 50 && abs(o, q) === a) hit.push(k); });
    return hit;
  }

  function play(state, idx, p) {
    if (state.result) return 'La partie est terminée.';
    if (state.turn !== idx) return "Ce n'est pas ton tour.";
    if (p.action === 'roll') {
      if (state.dice !== null) return 'Choisis un pion à déplacer.';
      const v = 1 + Math.floor(Math.random() * 6);
      const can = movable(state, idx, v);
      if (!can.length) {
        state.lastRoll = { by: idx, v, note: 'none' };
        state.lastMove = null;
        state.turn = 1 - idx;
      } else {
        state.dice = v;
        state.lastRoll = { by: idx, v, note: null };
      }
      return null;
    }
    if (state.dice === null) return "Lance d'abord le dé.";
    const k = p.pawn;
    if (!Number.isInteger(k) || !movable(state, idx, state.dice).includes(k)) return 'Ce pion ne peut pas bouger.';
    const v = state.dice;
    const from = state.pawns[idx][k];
    const to = from === -1 ? 0 : from + v;
    state.pawns[idx][k] = to;
    const hit = captureAt(state, idx, to);
    for (const q of hit) state.pawns[1 - idx][q] = -1;
    state.lastMove = { by: idx, pawn: k, from, to, captured: hit.length };
    state.dice = null;
    if (state.pawns[idx].every((x) => x === HOME)) {
      state.result = { winner: idx, reason: 'win' };
      return null;
    }
    const again = v === 6 || hit.length > 0 || to === HOME;
    if (!again) state.turn = 1 - idx;
    return null;
  }

  /* ---------------- Ordinateur ---------------- */

  /** Nombre de pions adverses qui pourraient atteindre la case absolue a avec un seul lancer (1 à 6). */
  function threats(state, i, a) {
    const o = 1 - i;
    let n = 0;
    for (const q of state.pawns[o]) {
      if (q < 0 || q > 50) continue;
      for (let v = 1; v <= 6; v++) {
        const t = q + v;
        if (t <= 50 && abs(o, t) === a) { n++; break; }
      }
    }
    return n;
  }

  function scoreMove(state, i, k, v, level) {
    const from = state.pawns[i][k];
    const to = from === -1 ? 0 : from + v;
    let s = Math.random() * 2;
    const hit = captureAt(state, i, to);
    if (hit.length) s += 100 + hit.reduce((acc, q) => acc + state.pawns[1 - i][q], 0);
    if (to === HOME) s += 70;
    else if (to >= 51) s += 35;
    if (from === -1) s += 45;
    s += to * 0.6;
    if (level >= 3) {
      if (to <= 50) {
        const a = abs(i, to);
        const safeNow = SAFE.has(a);
        const danger = safeNow ? 0 : threats(state, i, a);
        s -= danger * (35 + to * 0.4);
        if (safeNow) s += 12;
      }
      if (from >= 0 && from <= 50) {
        const a0 = abs(i, from);
        if (!SAFE.has(a0) && threats(state, i, a0)) s += 30 + from * 0.3; // fuir un pion menacé
      }
      // laisser un pion adverse proche de l'arrivée : le bloquer vaut cher, donc avancer ses pions de tête
      const lead = Math.max(...state.pawns[i]);
      if (from === lead) s += 4;
    }
    return s;
  }

  function cpu(state, level) {
    const i = state.turn;
    if (state.dice === null) return { action: 'roll' };
    const can = movable(state, i, state.dice);
    if (level <= 1) return { pawn: can[Math.floor(Math.random() * can.length)] };
    let best = can[0], bs = -Infinity;
    for (const k of can) {
      const s = scoreMove(state, i, k, state.dice, level);
      if (s > bs) { bs = s; best = k; }
    }
    return { pawn: best };
  }

  function view(state) {
    return {
      pawns: state.pawns,
      turn: state.turn,
      starter: state.starter,
      dice: state.dice,
      lastRoll: state.lastRoll,
      lastMove: state.lastMove,
      movable: state.dice !== null && !state.result ? movable(state, state.turn, state.dice) : [],
    };
  }

  return { init, play, cpu, view, movable, randomPayload: (s) => cpu(s, 1), START, SAFE };
})();
/* ================================================================== */
/* Comptes et sessions                                                 */
/* - mots de passe hachés avec scrypt (module crypto natif)            */
/* - jetons de session stockés sous forme de hash SHA-256              */
/* - persistance : PostgreSQL (DATABASE_URL) ou fichier JSON           */
/* ================================================================== */

const scrypt = promisify(crypto.scrypt);

const SESSION_MS = 30 * 24 * 3600 * 1000;
const RESERVED_PSEUDOS = new Set(['ordinateur', 'robot', 'admin', 'administrateur', 'moderateur', 'modérateur']);

const AVATARS = ['🦊', '🐼', '🐯', '🦁', '🐸', '🐙', '🦄', '🐧', '🐨', '🐵', '🦉', '🐢', '🐬', '🦖', '🚀', '⚡'];
const GAME_TYPES = ['p4', 'rps', 'dames', 'echecs', 'ludo'];

const emptyBucket = () => ({ w: 0, l: 0, d: 0 });
const emptyGameStats = () => ({ human: emptyBucket(), cpu: emptyBucket() });
const emptyStats = () => Object.fromEntries(GAME_TYPES.map((g) => [g, emptyGameStats()]));

const normPseudo = (p) => p.normalize('NFKC').toLowerCase();
const sha256 = (s) => crypto.createHash('sha256').update(s).digest('hex');

function validateRegistration(body) {
  const b = body && typeof body === 'object' ? body : {};

  const email = typeof b.email === 'string' ? b.email.trim().toLowerCase() : '';
  if (!email || email.length > 254 || !/^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(email)) {
    return { error: 'Adresse e-mail invalide.', field: 'email' };
  }

  const pseudo = typeof b.pseudo === 'string' ? b.pseudo.normalize('NFKC').trim().replace(/\s+/g, ' ') : '';
  if (pseudo.length < 3 || pseudo.length > 16) {
    return { error: 'Le pseudo doit faire entre 3 et 16 caractères.', field: 'pseudo' };
  }
  if (!/^[\p{L}\p{N}_\- ]+$/u.test(pseudo)) {
    return { error: 'Le pseudo ne peut contenir que des lettres, chiffres, espaces, _ et -.', field: 'pseudo' };
  }
  if (RESERVED_PSEUDOS.has(normPseudo(pseudo))) {
    return { error: 'Ce pseudo est réservé.', field: 'pseudo' };
  }

  const password = typeof b.password === 'string' ? b.password : '';
  if (password.length < 8 || password.length > 128) {
    return { error: 'Le mot de passe doit faire entre 8 et 128 caractères.', field: 'password' };
  }

  const avatar = AVATARS.includes(b.avatar) ? b.avatar : AVATARS[Math.floor(Math.random() * AVATARS.length)];
  return { email, pseudo, password, avatar };
}

class Store {
  constructor(file, opts = {}) {
    this.file = file;
    this.databaseUrl = opts.databaseUrl || null;
    this.mode = this.databaseUrl ? 'postgres' : 'fichier';
    this.pool = null;
    this.writing = Promise.resolve();
    this.users = {};
    this.sessions = {};
    this.byEmail = new Map();
    this.byPseudo = new Map();
    this.timer = null;
    this.dirty = false;
    if (!this.databaseUrl) this.load();
  }

  /** À appeler une fois avant d'accepter des connexions (charge la base PostgreSQL si elle est configurée). */
  async init() {
    if (!this.databaseUrl) return this.mode;
    let pg;
    try {
      pg = require('pg');
    } catch {
      throw new Error("le module 'pg' est introuvable (il doit figurer dans package.json)");
    }
    // Les hébergeurs (Neon, Supabase…) exigent SSL ; on retire sslmode de l'URL pour que notre réglage s'applique.
    const url = this.databaseUrl.replace(/([?&])sslmode=[^&]*&?/, '$1').replace(/[?&]$/, '');
    const local = /@(localhost|127\.0\.0\.1)[:/]/.test(url);
    this.pool = new pg.Pool({
      connectionString: url,
      ssl: local ? false : { rejectUnauthorized: false },
      max: 3,
      idleTimeoutMillis: 30000,
      connectionTimeoutMillis: 15000,
    });
    this.pool.on('error', (e) => console.error('[postgres]', e.message));
    await this.pool.query('CREATE TABLE IF NOT EXISTS arene_kv (k text PRIMARY KEY, v jsonb NOT NULL)');
    const res = await this.pool.query("SELECT v FROM arene_kv WHERE k = 'db'");
    if (res.rows.length) this.hydrate(res.rows[0].v);
    this.mode = 'postgres';
    return this.mode;
  }

  /** Repli sur le fichier si PostgreSQL est injoignable (le site démarre, mais les comptes ne seront pas durables). */
  fallbackToFile() {
    this.databaseUrl = null;
    this.pool = null;
    this.mode = 'fichier';
    this.load();
  }

  hydrate(data) {
    this.users = (data && data.users) || {};
    this.sessions = (data && data.sessions) || {};
    this.byEmail.clear();
    this.byPseudo.clear();
    const now = Date.now();
    for (const [key, s] of Object.entries(this.sessions)) if (!s || s.exp < now) delete this.sessions[key];
    for (const u of Object.values(this.users)) {
      // Les anciens comptes n'ont pas de statistiques pour les jeux ajoutés plus tard.
      const base = emptyStats();
      u.stats = Object.assign(base, u.stats || {});
      for (const g of GAME_TYPES) {
        u.stats[g] = Object.assign(emptyGameStats(), u.stats[g]);
        u.stats[g].human = Object.assign(emptyBucket(), u.stats[g].human);
        u.stats[g].cpu = Object.assign(emptyBucket(), u.stats[g].cpu);
      }
      this.byEmail.set(u.email, u.id);
      this.byPseudo.set(normPseudo(u.pseudo), u.id);
    }
  }

  load() {
    let raw;
    try {
      raw = fs.readFileSync(this.file, 'utf8');
    } catch (e) {
      if (e.code === 'ENOENT') return;
      throw e;
    }
    let data;
    try {
      data = JSON.parse(raw);
    } catch {
      const backup = `${this.file}.corrupt-${Date.now()}`;
      fs.renameSync(this.file, backup);
      console.error(`Base illisible : sauvegardée dans ${backup}. Démarrage avec une base vide.`);
      return;
    }
    this.hydrate(data);
  }

  save() {
    this.dirty = true;
    if (this.timer) return;
    this.timer = setTimeout(() => this.flush(), 250);
    this.timer.unref();
  }

  /** Écrit la base (fichier : synchrone ; PostgreSQL : la promesse retournée se termine à la fin de l'écriture). */
  flush() {
    clearTimeout(this.timer);
    this.timer = null;
    if (!this.dirty) return this.writing;
    this.dirty = false;
    const payload = JSON.stringify({ users: this.users, sessions: this.sessions });
    if (this.pool) {
      this.writing = this.writing
        .then(() => this.pool.query("INSERT INTO arene_kv (k, v) VALUES ('db', $1::jsonb) ON CONFLICT (k) DO UPDATE SET v = EXCLUDED.v", [payload]))
        .catch((e) => {
          console.error('Écriture PostgreSQL impossible (nouvel essai dans 5 s) :', e.message);
          this.dirty = true;
          if (!this.timer) {
            this.timer = setTimeout(() => this.flush(), 5000);
            this.timer.unref();
          }
        });
      return this.writing;
    }
    try {
      fs.mkdirSync(path.dirname(this.file), { recursive: true });
      const tmp = `${this.file}.tmp`;
      fs.writeFileSync(tmp, payload, { mode: 0o600 });
      fs.renameSync(tmp, this.file);
    } catch (e) {
      console.error('Écriture de la base impossible :', e.message);
    }
    return Promise.resolve();
  }

  async close() {
    await this.flush();
    if (this.pool) await this.pool.end().catch(() => {});
  }

  getUser(id) {
    return this.users[id] || null;
  }
  findByEmail(email) {
    const id = this.byEmail.get(email);
    return id ? this.users[id] : null;
  }
  emailTaken(email) {
    return this.byEmail.has(email);
  }
  pseudoTaken(pseudo) {
    return this.byPseudo.has(normPseudo(pseudo));
  }

  async createUser({ email, pseudo, password, avatar }) {
    const salt = crypto.randomBytes(16);
    const hash = await scrypt(password, salt, 64);
    // Revérification après l'attente : deux inscriptions simultanées ne doivent pas passer toutes les deux.
    if (this.emailTaken(email)) throw Object.assign(new Error('email'), { code: 'EMAIL_TAKEN' });
    if (this.pseudoTaken(pseudo)) throw Object.assign(new Error('pseudo'), { code: 'PSEUDO_TAKEN' });
    const user = {
      id: crypto.randomBytes(8).toString('hex'),
      email,
      pseudo,
      avatar,
      salt: salt.toString('hex'),
      hash: hash.toString('hex'),
      createdAt: Date.now(),
      stats: emptyStats(),
    };
    this.users[user.id] = user;
    this.byEmail.set(email, user.id);
    this.byPseudo.set(normPseudo(pseudo), user.id);
    this.save();
    return user;
  }

  async verifyPassword(user, password) {
    if (!user) {
      // Même durée de calcul que pour un vrai compte, pour ne pas révéler quels e-mails existent.
      await scrypt(password, Buffer.alloc(16), 64);
      return false;
    }
    const hash = await scrypt(password, Buffer.from(user.salt, 'hex'), 64);
    return crypto.timingSafeEqual(hash, Buffer.from(user.hash, 'hex'));
  }

  createSession(userId) {
    const token = crypto.randomBytes(32).toString('hex');
    const now = Date.now();
    const keys = Object.keys(this.sessions);
    if (keys.length > 5000) for (const k of keys) if (this.sessions[k].exp < now) delete this.sessions[k];
    this.sessions[sha256(token)] = { uid: userId, exp: now + SESSION_MS };
    this.save();
    return token;
  }

  getSession(token) {
    if (typeof token !== 'string') return null;
    const key = sha256(token);
    const s = this.sessions[key];
    if (!s) return null;
    if (s.exp < Date.now()) {
      delete this.sessions[key];
      return null;
    }
    return this.users[s.uid] || null;
  }

  deleteSession(token) {
    if (typeof token !== 'string') return;
    delete this.sessions[sha256(token)];
    this.save();
  }
}
/* ================================================================== */
/* Application installable (PWA) : manifeste, service worker, icônes    */
/* Tout est servi directement par le serveur : aucun autre fichier.     */
/* ================================================================== */

const MANIFEST = {
  name: 'Arène des jeux',
  short_name: 'Arène',
  description: "Puissance 4, Dames, Échecs, Ludo et Pierre-Feuille-Ciseaux : défie tes amis ou l'ordinateur.",
  lang: 'fr',
  start_url: '/',
  scope: '/',
  display: 'standalone',
  orientation: 'portrait',
  background_color: '#f1f5fb',
  theme_color: '#2563eb',
  icons: [
    { src: '/icons/icon-192.png', sizes: '192x192', type: 'image/png', purpose: 'any' },
    { src: '/icons/icon-512.png', sizes: '512x512', type: 'image/png', purpose: 'any' },
    { src: '/icons/icon-maskable-512.png', sizes: '512x512', type: 'image/png', purpose: 'maskable' },
  ],
};

const SERVICE_WORKER = `'use strict';
// Service worker minimal : l'application s'installe et son interface s'ouvre même avec un réseau lent.
// Les parties exigent une connexion : /socket.io et /api ne sont jamais mis en cache.
const CACHE = 'arene-v3';
self.addEventListener('install', (e) => { e.waitUntil(self.skipWaiting()); });
self.addEventListener('activate', (e) => {
  e.waitUntil(caches.keys().then((keys) => Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k)))).then(() => self.clients.claim()));
});
self.addEventListener('fetch', (e) => {
  const url = new URL(e.request.url);
  if (e.request.method !== 'GET' || url.origin !== location.origin) return;
  if (url.pathname.startsWith('/socket.io') || url.pathname.startsWith('/api') || url.pathname === '/healthz') return;
  e.respondWith(
    fetch(e.request)
      .then((res) => {
        if (res.ok) { const copy = res.clone(); caches.open(CACHE).then((c) => c.put(e.request, copy)); }
        return res;
      })
      .catch(() => caches.match(e.request).then((r) => r || caches.match('/'))),
  );
});
`;

const ICONS = {
  'icon-192.png': Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAMAAAADACAIAAADdvvtQAAAE9klEQVR42u3dMY4lRQyA4dkWRyAnIuEASAQcBImMI3COvQUSByFA4gDkxHAI8tHQ1KuyXe7u7w93Jdvt+qf69esZ16evf/r7DZjl0AIQCAQCgUAggEAgEAgEAgEEAoFAIBAIIBAIBAKBQACBQCAQCAQCgQACgUAgEAgEEAgEQnO+6FDEb5+//K//+v7nf/rU06qYXfW849PG6RwnrdnSrPF6WhWz16Q9Ar3UnYJOzdXTqphdGm0QaLpBGW1aLKZbPfUOlQq0vlqxnYqqp1UxxRodV7QnJFpgPa2KCY/WQqCMS1qJGV5Pq2IqHTouas9K5KR6WhVT5tDjvkhMbWvlvaMJx6UX7OprdoPmHDdY3fEsBfW0KqYgi3dh6CpQ5c1lJFdZPa2Kyc5lBwKBcD+B6h+OzjMW19OqmNSMdiAQCAQCgUAggEAgEAgEAq1Q/9vd5xmL62lVTGpGOxAIhFsKVLlRj+Qqq6dVMdm57EBoLFDNz9l4loJ6WhVTkOW4+gV0mFDx5OY87haW2tNL29xXoLy2zkVOqqdVMWU2H9f9uV+JGV5Pq2Iq98K6W1jsJa1HC6ynVTHFd1LzgcwHuppAbyaUXao5HQWa6JQZiT2f/nYKNNIsU1pNacWd8S4MBAKBQCAQCCAQCAQC4Rk4L+wD/vjrhw///duvftWcd3gX9v/ebDHJu7Cw7hR0alydAo28jU/pTlKn5tRJ0qhbc9p9iI4a9RgVZ92eqCANm9NOoG5HYkUtfEgo54VtuKSVmIH2rAd0Xti2i5mLHG7PSljnhW2+jFfjJ9kzF9xxT3g6zzovLHX7eTWF88KAJ50XVrD9jCdyXhhAILQVqNuRWGX3r5F0zgsDCAQCgUAgEAgEEAg3EqjbiUbFf5Fzns5xTwCB0Fygbicald3FRhI57gnIF6jbiUYFm9B4Csc9Ac87Lyx1E3o1uPPCNl/GXOQkh+bCOu5p28WsxAx3aCWg4542XNJ6tECH1kNd97in0g/RURcWFSfEoSgRuzVnEAOm3t4MmLqcQBOdMuKumzr7BRppliGbhmzizvgmGgQCgUAgEAggEAgEAuEZtDju6eQdwpYvf//88bsP//2bX37vU8yuet6x85vol15hFph0slT1KzdezF6T9gg0PS8sSaOXVit72eaK2aXRBoEWp83FOjS9WknLtlhPvUOlAgUOKgzRaN2ewGWLKqZYo+OK9oREC1yw9VCBxYRHayFQxpDUlZjhLV4JmLHeZQ4dF7VnJXJSc+fC5q10jUOP+yIxta2V944mpAuUPeG7eIL4tYQrEPq4weqOZylo6HiKmu0qO4t3YegqUOXNZSRX2QeUkUSVn5ZSc9mBQCDcT6D6h6PzjMUP2Ofp6p/28zLagUAgEAgEAoEAAoFAIBAItEL933OdZyz+bfPzdPW/+p6X0Q4EAuGWAlXexUZyld04RhJV3sVSc9mB0Figmk1oPEvBz/14ippNKDvL0Wd1r/K4d6HVLXD0cbew1J52mLdyw6ewvE1iLnLSMs+FzXOuxuaiHSjDoZWY4c1dCZix0mV7Yd0tLNah9WiBLV4PFbvelXdS84HMB7qaQG8mlOU49JQJZXMamZHY8+mvxXFPprTOmfT0Ka24Ad6FgUAgEAgEAgEEAoFAIBAIIBAIBAKBQACBQCAQCAQCCAQCgUAgEAgEEAgEAoFAIIBAIBC68y8OVpQ5m3xNawAAAABJRU5ErkJggg==', 'base64'),
  'icon-512.png': Buffer.from('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', 'base64'),
  'icon-maskable-512.png': Buffer.from('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', 'base64'),
};
ICONS['apple-touch-icon.png'] = ICONS['icon-192.png'];
/* Page web intégrée (générée depuis web/index.html par build.sh) */
const EMBEDDED_HTML = "<!doctype html>\n<html lang=\"fr\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1, viewport-fit=cover\">\n<meta name=\"theme-color\" content=\"#2563eb\">\n<meta name=\"apple-mobile-web-app-capable\" content=\"yes\">\n<meta name=\"apple-mobile-web-app-title\" content=\"Arène\">\n<title>Arène des jeux</title>\n<link rel=\"manifest\" href=\"/manifest.webmanifest\">\n<link rel=\"icon\" type=\"image/png\" href=\"/icons/icon-192.png\">\n<link rel=\"apple-touch-icon\" href=\"/apple-touch-icon.png\">\n<style>\n:root{\n  --bg:#eef3fb; --card:#ffffff; --soft:#f3f7fe; --line:#d6e0f0; --text:#0f1f3d; --muted:#586a88;\n  --primary:#1d5cf0; --primary-d:#1648c4; --on-primary:#ffffff; --primary-soft:#e3ecff;\n  --good:#12a150; --bad:#e03131; --warn:#f59f00;\n  --red:#ef4444; --yellow:#facc15; --blue:#2563eb;\n  --sq-light:#e6eeff; --sq-dark:#5b8cf5; --radius:16px;\n  --shadow:0 2px 6px rgba(20,50,110,.08),0 10px 24px rgba(20,50,110,.08);\n}\n*{box-sizing:border-box}\n[hidden]{display:none!important}\nhtml,body{margin:0;min-height:100%}\nbody{background:var(--bg);color:var(--text);font:16px/1.45 system-ui,-apple-system,\"Segoe UI\",Roboto,\"Helvetica Neue\",sans-serif;-webkit-tap-highlight-color:transparent}\nh1,h2,h3{margin:0 0 .5rem;line-height:1.2}\nh1{font-size:1.8rem}h2{font-size:1.1rem}\n.muted{color:var(--muted)}.small{font-size:.88rem}\nbutton{font:inherit}\n\n.topbar{display:flex;align-items:center;justify-content:space-between;gap:.6rem;padding:.65rem 1rem;padding-top:calc(.65rem + env(safe-area-inset-top,0px));background:linear-gradient(135deg,#1d5cf0,#3b82f6);color:#fff;position:sticky;top:0;z-index:5;box-shadow:0 2px 10px rgba(29,92,240,.35)}\n.brand{font-weight:800;font-size:1.15rem;letter-spacing:.2px;display:flex;align-items:center;gap:.5rem}\n.brand .logo{width:1.7rem;height:1.7rem;border-radius:8px;background:#fff;display:grid;place-items:center;font-size:1.05rem}\n.topbar-right{display:flex;align-items:center;gap:.5rem;min-width:0}\n.who{font-weight:600;font-size:.95rem;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:9rem}\nmain{max-width:980px;margin:0 auto;padding:1rem;padding-left:max(1rem,env(safe-area-inset-left,0px));padding-right:max(1rem,env(safe-area-inset-right,0px));padding-bottom:calc(1.5rem + env(safe-area-inset-bottom,0px))}\n.card{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);padding:1.1rem;margin-bottom:1rem;box-shadow:var(--shadow)}\n.row{display:flex;align-items:center;gap:.6rem}.between{justify-content:space-between}\n\n.btn{appearance:none;border:1px solid var(--line);background:#fff;color:var(--text);padding:.62rem 1rem;border-radius:12px;font-weight:700;cursor:pointer;transition:transform .08s,background .15s,border-color .15s,box-shadow .15s}\n.btn:hover{border-color:var(--primary)}\n.btn:active{transform:translateY(1px)}\n.btn:disabled{opacity:.55;cursor:not-allowed}\n.btn.primary{background:var(--primary);color:var(--on-primary);border-color:var(--primary);box-shadow:0 4px 12px rgba(29,92,240,.3)}\n.btn.primary:hover{background:var(--primary-d)}\n.btn.good{background:var(--good);color:#fff;border-color:var(--good)}\n.btn.danger{color:var(--bad);border-color:#f3c0c0}\n.btn.light{background:rgba(255,255,255,.18);color:#fff;border-color:rgba(255,255,255,.45)}\n.btn.small{padding:.35rem .7rem;font-size:.88rem;border-radius:10px}\n:focus-visible{outline:3px solid #ffb703;outline-offset:2px}\n\n/* Connexion */\n.auth-wrap{max-width:440px;margin:3vh auto 0}\n.hero{text-align:center;margin-bottom:1rem}\n.hero .logo-big{width:4.2rem;height:4.2rem;border-radius:20px;margin:0 auto .6rem;background:linear-gradient(135deg,#1d5cf0,#3b82f6);display:grid;place-items:center;font-size:2.2rem;box-shadow:0 8px 20px rgba(29,92,240,.35)}\n.tabs{display:flex;gap:.4rem;margin:1rem 0;background:var(--soft);padding:.3rem;border-radius:12px}\n.tab{flex:1;border:0;background:transparent;color:var(--muted);padding:.55rem;border-radius:9px;font-weight:700;cursor:pointer}\n.tab.active{background:#fff;color:var(--primary);box-shadow:0 1px 4px rgba(20,50,110,.15)}\n.form{display:grid;gap:.8rem}\n.form label,.form .label{display:grid;gap:.3rem;font-size:.92rem;color:var(--muted);font-weight:600}\ninput[type=text],input[type=email],input[type=password],input[type=search]{width:100%;padding:.7rem .8rem;border-radius:12px;border:1px solid var(--line);background:#fff;color:var(--text);font:inherit}\ninput:focus{outline:3px solid var(--primary-soft);border-color:var(--primary)}\n.err{color:var(--bad);font-size:.85rem;font-weight:600}\n.warnbox{background:#fff7e0;border:1px solid #ffd666;color:#7a5200;border-radius:12px;padding:.7rem .85rem;font-size:.88rem;margin-bottom:.8rem}\n.avatars{display:flex;flex-wrap:wrap;gap:.4rem}\n.avatar-opt{width:2.6rem;height:2.6rem;border-radius:12px;border:2px solid transparent;background:var(--soft);font-size:1.4rem;cursor:pointer;line-height:1}\n.avatar-opt.selected{border-color:var(--primary);background:var(--primary-soft)}\n\n/* Salon */\n.lobby-grid{display:grid;grid-template-columns:1fr 1.1fr;gap:1rem;align-items:start}\n@media(max-width:760px){.lobby-grid{grid-template-columns:1fr}}\n.me-head{display:flex;align-items:center;gap:.8rem}\n.big-avatar{font-size:2.2rem;background:var(--primary-soft);border-radius:18px;width:3.6rem;height:3.6rem;display:grid;place-items:center;border:0;cursor:pointer}\n.me-name{font-size:1.2rem;font-weight:800}\n.stats{width:100%;border-collapse:collapse;margin-top:.9rem;font-size:.88rem}\n.stats th,.stats td{text-align:left;padding:.4rem .3rem;border-bottom:1px solid var(--line)}\n.stats thead th{color:var(--muted);font-weight:700;font-size:.78rem}\n.stats td{font-variant-numeric:tabular-nums;white-space:nowrap}\n.pill{background:var(--primary-soft);color:var(--primary);border-radius:999px;padding:.15rem .65rem;font-size:.82rem;font-weight:700}\n.gamegrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(8.2rem,1fr));gap:.5rem;margin:.6rem 0}\n.gbtn{border:2px solid var(--line);background:#fff;border-radius:14px;padding:.6rem .4rem;font-weight:700;cursor:pointer;display:grid;gap:.15rem;justify-items:center;text-align:center;font-size:.9rem}\n.gbtn .ic{font-size:1.5rem;line-height:1}\n.gbtn[aria-pressed=true]{border-color:var(--primary);background:var(--primary-soft);color:var(--primary-d)}\n.gbtn:hover{border-color:var(--primary)}\n.levels{display:grid;grid-template-columns:repeat(3,1fr);gap:.5rem}\n.level{display:grid;gap:.1rem;padding:.7rem .4rem;border-radius:12px;border:0;background:var(--primary);color:#fff;cursor:pointer;text-align:center;box-shadow:0 4px 10px rgba(29,92,240,.25)}\n.level:nth-child(2){background:#7c3aed;box-shadow:0 4px 10px rgba(124,58,237,.25)}\n.level:nth-child(3){background:#e8590c;box-shadow:0 4px 10px rgba(232,89,12,.25)}\n.level strong{font-size:1rem}.level span{font-size:.78rem;opacity:.9}\n.players{list-style:none;margin:.8rem 0 0;padding:0;display:grid;gap:.5rem;max-height:55vh;overflow:auto}\n.player{display:flex;align-items:center;gap:.6rem;padding:.55rem .65rem;border-radius:12px;background:var(--soft);border:1px solid var(--line)}\n.player .av{font-size:1.5rem}\n.player .nm{font-weight:700;flex:1;min-width:0;overflow-wrap:anywhere}\n.linkbtn{background:none;border:0;color:var(--primary);font-weight:700;cursor:pointer;padding:0;text-decoration:underline}\n\n/* Partie */\n.game-card{max-width:640px;margin:0 auto}\n.game-title{display:flex;align-items:center;justify-content:space-between;gap:.5rem;margin-bottom:.6rem}\n.game-head{display:grid;grid-template-columns:minmax(0,1fr) auto minmax(0,1fr);align-items:center;gap:.4rem;margin-bottom:.7rem}\n.gp{display:flex;align-items:center;gap:.5rem;padding:.45rem .55rem;border-radius:12px;border:2px solid transparent;background:var(--soft);min-width:0}\n.gp.right{justify-content:flex-end;text-align:right;flex-direction:row-reverse}\n.gp.active{border-color:var(--primary);background:var(--primary-soft)}\n.gp .av{font-size:1.5rem}\n.gp .info{min-width:0}\n.gp .nm{font-weight:800;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:.95rem}\n.gp .sub{font-size:.75rem;color:var(--muted)}\n.token{width:.85rem;height:.85rem;border-radius:50%;display:inline-block;vertical-align:middle;border:1px solid rgba(0,0,0,.25)}\n.token.t0{background:var(--red)}.token.t1{background:var(--yellow)}.token.white{background:#fff}.token.black{background:#1f2937}\n.vs{color:var(--muted);font-weight:800;font-size:.85rem}\n.status{text-align:center;min-height:1.7rem;font-weight:800;margin-bottom:.6rem}\n.status .timer{color:var(--muted);font-weight:600;margin-left:.4rem;font-variant-numeric:tabular-nums}\n.status .timer.low{color:var(--bad)}\n.alert{color:var(--bad)}\n\n.board4{display:grid;grid-template-columns:repeat(7,1fr);gap:6px;background:var(--blue);padding:8px;border-radius:16px;max-width:460px;margin:0 auto;box-shadow:0 8px 0 #1648c4}\n.colbtn{display:grid;gap:6px;padding:0;border:0;background:transparent;cursor:pointer;border-radius:10px}\n.colbtn:disabled{cursor:default}\n.colbtn.can:hover{background:rgba(255,255,255,.2)}\n.cell{aspect-ratio:1;border-radius:50%;background:#eaf1ff;box-shadow:inset 0 3px 5px rgba(0,0,0,.25)}\n.cell.p1{background:var(--red);box-shadow:inset 0 -4px 0 rgba(0,0,0,.2)}\n.cell.p2{background:var(--yellow);box-shadow:inset 0 -4px 0 rgba(0,0,0,.15)}\n.cell.last{outline:3px solid #fff;outline-offset:-3px}\n.cell.win{animation:pulse .8s infinite alternate;outline:4px solid #fff;outline-offset:-4px}\n@keyframes pulse{to{transform:scale(.88)}}\n\n.rps-scores{display:flex;justify-content:center;align-items:baseline;gap:1rem;font-size:2.4rem;font-weight:900;font-variant-numeric:tabular-nums;margin:.2rem 0 .8rem}\n.rps-scores small{font-size:.9rem;color:var(--muted);font-weight:600}\n.rps-reveal{display:flex;justify-content:center;align-items:center;gap:1.4rem;font-size:3.4rem;min-height:5rem;margin-bottom:.4rem}\n.rps-reveal .who2{display:grid;text-align:center;font-size:.8rem;color:var(--muted)}\n.rps-reveal .win{filter:drop-shadow(0 0 10px var(--good));transform:scale(1.12)}\n.rps-choices{display:grid;grid-template-columns:repeat(3,1fr);gap:.6rem}\n.rps-btn{padding:1rem .4rem;border-radius:16px;border:2px solid var(--line);background:#fff;color:var(--text);font-weight:700;cursor:pointer;display:grid;gap:.3rem;justify-items:center}\n.rps-btn .em{font-size:2.6rem;line-height:1}\n.rps-btn:hover:not(:disabled){border-color:var(--primary)}\n.rps-btn.chosen{border-color:var(--good);background:#e6f8ee}\n.rps-btn:disabled{cursor:default;opacity:.75}\n\n/* Échecs et dames */\n.chess,.draughts{display:grid;margin:0 auto;border:3px solid #173a8a;border-radius:8px;overflow:hidden;width:100%;max-width:520px;aspect-ratio:1;box-shadow:var(--shadow)}\n.chess{grid-template-columns:repeat(8,minmax(0,1fr));grid-template-rows:repeat(8,minmax(0,1fr))}.draughts{grid-template-columns:repeat(10,minmax(0,1fr));grid-template-rows:repeat(10,minmax(0,1fr))}\n.sq{position:relative;border:0;padding:0;margin:0;display:grid;place-items:center;cursor:default;background:var(--sq-light);font:inherit;min-width:0;min-height:0;overflow:hidden}\n.sq.dark{background:var(--sq-dark)}\n.sq.last{background:#fbe88a}.sq.dark.last{background:#e3bc2f}\n.sq.sel{background:#ffd43b}.sq.dark.sel{background:#f5a400}\n.sq.check{background:#ff8a80}.sq.dark.check{background:#e53935}\n.sq.clickable{cursor:pointer}\n.sq.tgt::after{content:\"\";position:absolute;width:30%;height:30%;border-radius:50%;background:rgba(15,31,61,.35)}\n.sq.tgt.cap::after{width:88%;height:88%;background:transparent;border:5px solid rgba(15,31,61,.4)}\n.pc{font-size:min(8.6vw,3rem);line-height:1;z-index:1;user-select:none}\n.pc.w{color:#fff;text-shadow:0 0 2px #0b1b3f,0 0 2px #0b1b3f,0 1px 3px rgba(0,0,0,.6)}\n.pc.b{color:#101a33;text-shadow:0 0 1px rgba(255,255,255,.7)}\n.dm{width:78%;aspect-ratio:1;border-radius:50%;z-index:1;display:grid;place-items:center;font-size:min(4vw,1.4rem);box-shadow:inset 0 -4px 0 rgba(0,0,0,.25),0 2px 4px rgba(0,0,0,.35)}\n.dm.w{background:#fff;color:#c28a00;border:2px solid #cdd6ea}\n.dm.b{background:#1b2540;color:#ffd43b;border:2px solid #0b1224}\n\n/* Ludo */\n.ludo{position:relative;display:grid;grid-template-columns:repeat(15,1fr);grid-template-rows:repeat(15,1fr);aspect-ratio:1;width:100%;max-width:540px;margin:0 auto;border:3px solid #173a8a;border-radius:10px;overflow:hidden;background:#fff}\n.yard{border:0;display:grid;place-items:center}\n.yard.y0{background:#fecaca}.yard.y1{background:#fef08a}.yard.yx{background:#e8edf6}\n.yard::before{content:\"\";width:62%;height:62%;background:rgba(255,255,255,.8);border-radius:14px}\n.tk{background:#fff;border:1px solid #cfd9ec;display:grid;place-items:center;font-size:min(2.6vw,.9rem);color:#7a8aa8}\n.tk.s0{background:#fca5a5}.tk.s1{background:#fde047}\n.hc0{background:#fca5a5;border:1px solid #f08a8a}.hc1{background:#fde047;border:1px solid #e8c800}\n.centerbox{background:conic-gradient(from 45deg,#fecaca 0 25%,#fde68a 25% 50%,#fecaca 50% 75%,#fde68a 75% 100%);border:1px solid #cfd9ec;display:grid;place-items:center;font-size:min(5vw,1.6rem)}\n.slot{border-radius:50%;background:rgba(255,255,255,.95);width:78%;height:78%;align-self:center;justify-self:center;box-shadow:inset 0 2px 4px rgba(0,0,0,.2)}\n.pawn{align-self:center;justify-self:center;width:84%;aspect-ratio:1;border-radius:50%;border:2px solid #fff;padding:0;z-index:2;cursor:default;display:grid;place-items:center;font-weight:900;font-size:min(3vw,.95rem);color:#fff;box-shadow:0 2px 4px rgba(0,0,0,.45);text-shadow:0 1px 1px rgba(0,0,0,.5)}\n.pawn.p0{background:#dc2626}.pawn.p1{background:#d99a00}\n.pawn.can{cursor:pointer;animation:halo 1s infinite;box-shadow:0 0 0 3px #1d5cf0,0 0 0 3px rgba(29,92,240,.55)}\n@keyframes halo{to{box-shadow:0 0 0 3px #1d5cf0,0 0 0 11px rgba(29,92,240,0)}}\n.dice-zone{display:flex;align-items:center;justify-content:center;gap:1rem;margin:.9rem 0 .2rem;flex-wrap:wrap}\n.die{font-size:3.6rem;line-height:1;width:5rem;height:5rem;display:grid;place-items:center;background:#fff;border:2px solid var(--line);border-radius:16px;box-shadow:var(--shadow)}\n.die.rolling{animation:spin .5s linear}\n@keyframes spin{from{transform:rotate(0)}to{transform:rotate(360deg)}}\n.pawnpick{display:flex;gap:.5rem;justify-content:center;flex-wrap:wrap;margin-top:.6rem}\n.legend{display:flex;gap:1rem;justify-content:center;font-size:.8rem;color:var(--muted);margin-top:.5rem;flex-wrap:wrap}\n\n.banner{margin:1rem 0 .2rem;padding:.9rem;border-radius:14px;text-align:center;font-weight:800;font-size:1.15rem;background:var(--soft)}\n.banner.win{background:#e0f7ea;color:#0b7a3b}.banner.lose{background:#fde8e8;color:#b42323}\n.game-actions{display:flex;flex-wrap:wrap;gap:.6rem;justify-content:center;margin-top:.9rem}\n.notice{text-align:center;color:var(--muted);font-size:.88rem;margin-top:.6rem}\n\n.overlay{position:fixed;inset:0;background:rgba(10,25,60,.55);display:grid;place-items:center;z-index:20;padding:1rem}\n.modal{background:#fff;border-radius:20px;padding:1.3rem;max-width:400px;width:100%;max-height:88vh;overflow:auto;box-shadow:0 20px 50px rgba(0,0,0,.3)}\n.modal.center{text-align:center}\n.modal .big{font-size:3rem}\n.modal .actions{display:flex;gap:.6rem;justify-content:center;margin-top:1rem;flex-wrap:wrap}\n.modal ul.rules{margin:.5rem 0 0;padding-left:1.1rem;display:grid;gap:.35rem;font-size:.95rem}\n.bar{height:6px;border-radius:6px;background:var(--soft);overflow:hidden;margin-top:.9rem}\n.bar>i{display:block;height:100%;width:100%;background:var(--primary);transform-origin:left}\n.promo{display:flex;gap:.5rem;justify-content:center;margin-top:.8rem}\n.promo button{width:3.6rem;height:3.6rem;font-size:2.2rem;border-radius:12px;border:2px solid var(--line);background:var(--sq-light);cursor:pointer}\n.promo button:hover{border-color:var(--primary)}\n.picklist{display:grid;gap:.5rem;margin-top:.8rem}\n.picklist .btn{display:flex;align-items:center;gap:.7rem;text-align:left}\n\n.toasts{position:fixed;bottom:calc(1rem + env(safe-area-inset-bottom,0px));left:50%;transform:translateX(-50%);display:grid;gap:.5rem;z-index:30;width:min(92vw,420px)}\n.toast{background:#10224a;color:#fff;padding:.7rem 1rem;border-radius:12px;font-weight:600;box-shadow:0 6px 20px rgba(0,0,0,.3)}\n.toast.error{background:var(--bad)}\n@media(prefers-reduced-motion:reduce){.cell.win,.pawn.can,.die.rolling{animation:none}*{transition:none!important}}\n</style>\n</head>\n<body>\n<header class=\"topbar\" id=\"topbar\" hidden>\n  <div class=\"brand\"><span class=\"logo\">🎮</span>Arène des jeux</div>\n  <div class=\"topbar-right\">\n    <button class=\"btn small light\" id=\"install\" hidden>Installer</button>\n    <span class=\"who\" id=\"who\"></span>\n    <button class=\"btn small light\" id=\"logout\">Déconnexion</button>\n  </div>\n</header>\n\n<main id=\"app\">\n  <section id=\"screen-auth\" class=\"screen\" hidden>\n    <div class=\"auth-wrap\">\n      <div class=\"hero\">\n        <div class=\"logo-big\">🎮</div>\n        <h1>Arène des jeux</h1>\n        <p class=\"muted\">Puissance 4, Dames, Échecs, Ludo et Pierre-Feuille-Ciseaux.<br>Défie tes amis ou l'ordinateur.</p>\n      </div>\n      <div class=\"card\">\n        <div class=\"warnbox\" id=\"warn-storage\" hidden>⚠️ Les comptes ne sont pas conservés sur ce serveur : ils sont effacés à chaque redémarrage. Si ton compte ne marche plus, inscris-toi à nouveau.</div>\n        <div class=\"tabs\" role=\"tablist\">\n          <button class=\"tab active\" data-tab=\"register\" role=\"tab\">Inscription</button>\n          <button class=\"tab\" data-tab=\"login\" role=\"tab\">Connexion</button>\n        </div>\n        <form id=\"form-register\" class=\"form\" novalidate>\n          <label>Adresse e-mail<input type=\"email\" name=\"email\" autocomplete=\"email\" required><span class=\"err\" data-for=\"email\"></span></label>\n          <label>Pseudo (3 à 16 caractères)<input type=\"text\" name=\"pseudo\" autocomplete=\"nickname\" maxlength=\"16\" required><span class=\"err\" data-for=\"pseudo\"></span></label>\n          <label>Mot de passe (8 caractères minimum)<input type=\"password\" name=\"password\" autocomplete=\"new-password\" required><span class=\"err\" data-for=\"password\"></span></label>\n          <div class=\"label\">Ton avatar</div>\n          <div class=\"avatars\" id=\"avatar-register\"></div>\n          <div class=\"err\" id=\"err-register\"></div>\n          <button class=\"btn primary\" type=\"submit\">Créer mon profil</button>\n        </form>\n        <form id=\"form-login\" class=\"form\" novalidate hidden>\n          <label>Adresse e-mail<input type=\"email\" name=\"email\" autocomplete=\"email\" required></label>\n          <label>Mot de passe<input type=\"password\" name=\"password\" autocomplete=\"current-password\" required></label>\n          <div class=\"err\" id=\"err-login\"></div>\n          <button class=\"btn primary\" type=\"submit\">Se connecter</button>\n        </form>\n      </div>\n    </div>\n  </section>\n\n  <section id=\"screen-lobby\" class=\"screen\" hidden>\n    <div class=\"lobby-grid\">\n      <div>\n        <div class=\"card\" id=\"me-card\"></div>\n        <div class=\"card\">\n          <div class=\"row between\"><h2>Jouer contre l'ordinateur</h2><button class=\"linkbtn\" id=\"cpu-rules\">Règles</button></div>\n          <div class=\"gamegrid\" id=\"cpu-game\"></div>\n          <div class=\"levels\" id=\"cpu-levels\">\n            <button class=\"level\" data-level=\"1\"><strong>Niveau 1</strong><span>Débutant</span></button>\n            <button class=\"level\" data-level=\"2\"><strong>Niveau 2</strong><span>Malin</span></button>\n            <button class=\"level\" data-level=\"3\"><strong>Niveau 3</strong><span>Redoutable</span></button>\n          </div>\n        </div>\n      </div>\n      <div class=\"card\">\n        <div class=\"row between\"><h2>Joueurs libres</h2><span class=\"pill\" id=\"online-count\"></span></div>\n        <input type=\"search\" id=\"search\" placeholder=\"Chercher un joueur…\" aria-label=\"Chercher un joueur\">\n        <ul class=\"players\" id=\"players\"></ul>\n        <p class=\"muted small\" id=\"players-empty\" hidden></p>\n      </div>\n    </div>\n  </section>\n\n  <section id=\"screen-game\" class=\"screen\" hidden>\n    <div class=\"card game-card\" id=\"game\"></div>\n  </section>\n</main>\n\n<div class=\"overlay\" id=\"overlay\" hidden><div class=\"modal\" id=\"modal\" role=\"dialog\" aria-modal=\"true\"></div></div>\n<div class=\"toasts\" id=\"toasts\" aria-live=\"polite\"></div>\n\n<script src=\"/socket.io/socket.io.js\"></script>\n<script>\n'use strict';\n(() => {\n  const TOKEN_KEY = 'arene.token';\n  const GAMES = {\n    p4: { name: 'Puissance 4', icon: '🔴', rules: ['Aligne 4 pions de ta couleur : en ligne, en colonne ou en diagonale.', 'Chacun son tour, tu choisis une colonne et le pion tombe tout en bas.', 'Grille pleine sans alignement : match nul.', 'Contre un joueur : 30 secondes par coup (sinon un coup au hasard est joué).'] },\n    rps: { name: 'Pierre-Feuille-Ciseaux', icon: '✊', rules: ['Pierre bat ciseaux, ciseaux bat feuille, feuille bat pierre.', 'Le premier à gagner 2 manches remporte la partie.', 'En cas d\\'égalité, la manche est rejouée.', 'Contre un joueur : 15 secondes par manche.'] },\n    dames: { name: 'Dames', icon: '⚫', rules: ['Dames internationales sur un plateau de 10 × 10. Les blancs commencent.', 'Un pion avance d\\'une case en diagonale et prend en avant comme en arrière.', 'La prise est obligatoire, et il faut prendre le plus de pièces possible.', 'Un pion qui termine son coup sur la dernière rangée devient dame.', 'La dame se déplace et prend de loin, en diagonale.', 'Tu perds si tu n\\'as plus de pièces ou plus de coup possible. Contre un joueur : 60 secondes par coup.'] },\n    echecs: { name: 'Échecs', icon: '♞', rules: ['Règles complètes : roque, prise en passant, promotion du pion.', 'Touche une pièce, puis une case marquée pour la jouer. Le roi en échec est signalé en rouge.', 'Échec et mat : tu gagnes. Pat, répétition de position, règle des 50 coups ou matériel insuffisant : match nul.', 'Le joueur qui commence a les blancs. Contre un joueur : 2 minutes par coup.'] },\n    ludo: { name: 'Ludo', icon: '🎲', rules: ['2 joueurs, 4 pions chacun. Lance le dé : il faut un 6 pour sortir un pion.', 'Un 6, une capture ou l\\'arrivée d\\'un pion à la maison te font rejouer.', 'Tu captures un pion adverse en tombant sur sa case (sauf sur une case ★ ou une case de départ) : il retourne à l\\'écurie.', 'Il faut le nombre exact pour entrer dans la maison. Le premier qui rentre ses 4 pions gagne.', 'Contre un joueur : 40 secondes par action.'] },\n  };\n  const GAME_IDS = Object.keys(GAMES);\n  const EMOJI = { pierre: '✊', feuille: '✋', ciseaux: '✌️' };\n  const LABEL = { pierre: 'Pierre', feuille: 'Feuille', ciseaux: 'Ciseaux' };\n  const VS = '︎'; // force l'affichage \"texte\" des symboles d'échecs (pas d'emoji)\n  const CHESS = { 1: '♟', 2: '♞', 3: '♝', 4: '♜', 5: '♛', 6: '♚' };\n  const DIE = ['', '⚀', '⚁', '⚂', '⚃', '⚄', '⚅'];\n  const REASONS = {\n    checkmate: 'Échec et mat !', stalemate: 'Pat : personne ne peut jouer, match nul.', fifty: 'Nulle : trop de coups sans progrès.',\n    repetition: 'Nulle : même position répétée 3 fois.', material: 'Nulle : matériel insuffisant pour mater.', full: 'Grille pleine.',\n  };\n\n  const $ = (s, r = document) => r.querySelector(s);\n  const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));\n\n  /** Crée un élément ; tout le texte passe par textContent (aucune injection HTML possible). */\n  function h(tag, props, ...children) {\n    const el = document.createElement(tag);\n    for (const [k, v] of Object.entries(props || {})) {\n      if (v == null || v === false) continue;\n      if (k === 'class') el.className = v;\n      else if (k === 'on') for (const [ev, fn] of Object.entries(v)) el.addEventListener(ev, fn);\n      else if (k === 'grid') { el.style.gridRow = String(v[0]); el.style.gridColumn = String(v[1]); }\n      else if (k in el && k !== 'list') el[k] = v;\n      else el.setAttribute(k, v === true ? '' : v);\n    }\n    for (const c of children.flat()) {\n      if (c == null || c === false) continue;\n      el.append(c.nodeType ? c : document.createTextNode(String(c)));\n    }\n    return el;\n  }\n\n  const store = {\n    get() { try { return localStorage.getItem(TOKEN_KEY); } catch { return null; } },\n    set(t) { try { localStorage.setItem(TOKEN_KEY, t); } catch { /* indisponible */ } },\n    clear() { try { localStorage.removeItem(TOKEN_KEY); } catch { /* ignore */ } },\n  };\n\n  const state = {\n    token: store.get(), socket: null, me: null, lobby: { players: [], online: 0 }, game: null, gameDeadline: null,\n    invite: null, inviteDeadline: null, cpuGame: 'p4', search: '', registerAvatar: null, ignoreDisconnect: false,\n    sel: null, // case sélectionnée (échecs / dames)\n    rolling: false, installEvent: null,\n  };\n  const emptyStats = () => Object.fromEntries(GAME_IDS.map((g) => [g, { human: { w: 0, l: 0, d: 0 }, cpu: { w: 0, l: 0, d: 0 } }]));\n\n  /* ---------------- Interface générale ---------------- */\n\n  function toast(msg, kind) {\n    const t = h('div', { class: `toast ${kind || ''}`, role: 'status' }, msg);\n    $('#toasts').append(t);\n    setTimeout(() => t.remove(), 3800);\n  }\n  function showScreen(name) {\n    for (const s of $$('.screen')) s.hidden = s.id !== `screen-${name}`;\n    $('#topbar').hidden = name === 'auth';\n  }\n  function openModal(...nodes) {\n    $('#modal').className = 'modal';\n    $('#modal').replaceChildren(...nodes);\n    $('#overlay').hidden = false;\n  }\n  function closeModal() {\n    $('#overlay').hidden = true;\n    $('#modal').replaceChildren();\n  }\n\n  function api(path, body) {\n    return fetch(path, {\n      method: 'POST',\n      headers: { 'Content-Type': 'application/json', ...(state.token ? { Authorization: `Bearer ${state.token}` } : {}) },\n      body: JSON.stringify(body || {}),\n    }).then(async (r) => {\n      let data = {};\n      try { data = await r.json(); } catch { /* corps vide */ }\n      if (!r.ok) throw Object.assign(new Error(data.error || 'Erreur réseau.'), { field: data.field });\n      return data;\n    });\n  }\n  function emit(event, payload) {\n    return new Promise((resolve) => {\n      if (!state.socket) return resolve({ ok: false });\n      state.socket.timeout(8000).emit(event, payload || {}, (err, res) => {\n        if (err) { toast('Le serveur ne répond pas.', 'error'); return resolve({ ok: false }); }\n        if (res && !res.ok && res.error) toast(res.error, 'error');\n        resolve(res || { ok: false });\n      });\n    });\n  }\n\n  function showRules(gameId) {\n    const g = GAMES[gameId];\n    openModal(h('h2', {}, `${g.icon} ${g.name}`), h('ul', { class: 'rules' }, g.rules.map((r) => h('li', {}, r))),\n      h('div', { class: 'actions' }, h('button', { class: 'btn primary', on: { click: closeModal } }, 'Compris')));\n  }\n\n  /* ---------------- Bouton « retour » du téléphone ---------------- */\n  // Pile d'historique : [base, app]. Un appui sur « retour » ramène à « base » : on le traite, puis on remet « app ».\n  const nav = { armed: false, timer: null };\n  function initHistory() {\n    try {\n      history.replaceState({ s: 'base' }, '');\n      history.pushState({ s: 'app' }, '');\n    } catch { return; }\n    window.addEventListener('popstate', () => {\n      if (!$('#overlay').hidden) { // une fenêtre est ouverte : retour = la fermer\n        closeModal();\n        history.pushState({ s: 'app' }, '');\n        return;\n      }\n      const g = state.game;\n      if (g) {\n        history.pushState({ s: 'app' }, '');\n        if (g.over || g.vsCpu) return leave(true);\n        return askLeave();\n      }\n      if (nav.armed) { // deuxième appui rapproché : on laisse sortir\n        clearTimeout(nav.timer);\n        return history.back();\n      }\n      nav.armed = true;\n      toast('Appuie encore sur « retour » pour quitter');\n      nav.timer = setTimeout(() => { nav.armed = false; }, 2500);\n      history.pushState({ s: 'app' }, '');\n    });\n  }\n  function askLeave() {\n    openModal(h('h2', {}, 'Quitter la partie ?'), h('p', { class: 'muted' }, 'Si tu quittes maintenant, tu perds la partie.'),\n      h('div', { class: 'actions' },\n        h('button', { class: 'btn', on: { click: closeModal } }, 'Continuer à jouer'),\n        h('button', { class: 'btn danger', on: { click: () => { closeModal(); leave(true); } } }, 'Quitter')));\n  }\n\n  /* ---------------- Authentification ---------------- */\n\n  function renderAvatarPicker(container, avatars, onPick) {\n    container.replaceChildren();\n    for (const a of avatars) {\n      const b = h('button', { type: 'button', class: 'avatar-opt', 'aria-label': `Avatar ${a}`, on: { click: () => onPick(a) } }, a);\n      b.dataset.avatar = a;\n      container.append(b);\n    }\n  }\n  const markAvatar = (container, sel) => { for (const b of $$('.avatar-opt', container)) b.classList.toggle('selected', b.dataset.avatar === sel); };\n\n  async function initAuthScreen() {\n    let avatars = ['🦊', '🐼', '🐯', '🦁', '🐸', '🐙'];\n    try {\n      const cfg = await (await fetch('/api/config')).json();\n      avatars = cfg.avatars || avatars;\n      $('#warn-storage').hidden = cfg.persistent !== false;\n    } catch { /* valeurs par défaut */ }\n    state.registerAvatar = avatars[Math.floor(Math.random() * avatars.length)];\n    const box = $('#avatar-register');\n    renderAvatarPicker(box, avatars, (a) => { state.registerAvatar = a; markAvatar(box, a); });\n    markAvatar(box, state.registerAvatar);\n\n    for (const tab of $$('.tab')) {\n      tab.addEventListener('click', () => {\n        $$('.tab').forEach((t) => t.classList.toggle('active', t === tab));\n        $('#form-register').hidden = tab.dataset.tab !== 'register';\n        $('#form-login').hidden = tab.dataset.tab !== 'login';\n      });\n    }\n    $('#form-register').addEventListener('submit', async (e) => {\n      e.preventDefault();\n      const f = e.target;\n      $$('.err', f).forEach((x) => (x.textContent = ''));\n      const btn = $('button[type=submit]', f);\n      btn.disabled = true;\n      try {\n        onAuthenticated(await api('/api/register', { email: f.email.value, pseudo: f.pseudo.value, password: f.password.value, avatar: state.registerAvatar }));\n      } catch (err) {\n        const target = err.field ? $(`.err[data-for=\"${err.field}\"]`, f) : null;\n        (target || $('#err-register')).textContent = err.message;\n      } finally { btn.disabled = false; }\n    });\n    $('#form-login').addEventListener('submit', async (e) => {\n      e.preventDefault();\n      const f = e.target;\n      $('#err-login').textContent = '';\n      const btn = $('button[type=submit]', f);\n      btn.disabled = true;\n      try { onAuthenticated(await api('/api/login', { email: f.email.value, password: f.password.value })); }\n      catch (err) { $('#err-login').textContent = err.message; }\n      finally { btn.disabled = false; }\n    });\n  }\n\n  function onAuthenticated(res) {\n    state.token = res.token;\n    store.set(res.token);\n    state.me = res.me;\n    connect();\n  }\n\n  function logoutLocal(message) {\n    state.ignoreDisconnect = true;\n    if (state.socket) state.socket.disconnect();\n    state.socket = null; state.token = null; state.me = null; state.game = null; state.invite = null;\n    store.clear();\n    closeModal();\n    showScreen('auth');\n    if (message) toast(message);\n  }\n\n  /* ---------------- Temps réel ---------------- */\n\n  function connect() {\n    if (state.socket) state.socket.disconnect();\n    state.ignoreDisconnect = false;\n    const socket = io({ auth: { token: state.token }, reconnectionDelayMax: 3000 });\n    state.socket = socket;\n    socket.on('connect_error', (err) => { if (err && err.message === 'unauthorized') logoutLocal('Session expirée, reconnecte-toi.'); });\n    socket.on('init', (d) => {\n      state.me = d.me; state.lobby = d.lobby; state.game = d.game; state.sel = null;\n      state.gameDeadline = d.game && d.game.timeLeft != null ? Date.now() + d.game.timeLeft : null;\n      state.invite = null;\n      closeModal();\n      if (d.invite) onInviteNew(d.invite);\n      renderAll();\n    });\n    socket.on('lobby:update', (l) => { state.lobby = l; if (!state.game) renderPlayers(); });\n    socket.on('me:update', (u) => { Object.assign(state.me, u); if (!state.game) renderMe(); $('#who').textContent = state.me.pseudo; });\n    socket.on('invite:new', onInviteNew);\n    socket.on('invite:ended', onInviteEnded);\n    socket.on('game:state', (g) => {\n      const prev = state.game;\n      const rolled = prev && prev.id === g.id && g.type === 'ludo' && g.lastRoll && (!prev.lastRoll || prev.lastRoll.v !== g.lastRoll.v || prev.lastRoll.by !== g.lastRoll.by || prev.dice !== g.dice);\n      state.game = g; state.sel = null;\n      state.gameDeadline = g.timeLeft != null ? Date.now() + g.timeLeft : null;\n      state.rolling = !!rolled;\n      closeModal(); state.invite = null;\n      renderAll();\n    });\n    socket.on('session:replaced', () => logoutLocal(\"Tu t'es connecté ailleurs : cette fenêtre est déconnectée.\"));\n    socket.on('disconnect', () => { if (!state.ignoreDisconnect) toast('Connexion perdue, reconnexion…'); });\n  }\n\n  /* ---------------- Invitations ---------------- */\n\n  function onInviteNew(inv) {\n    state.invite = inv;\n    state.inviteDeadline = Date.now() + inv.timeLeft;\n    const incoming = inv.to.id === state.me.id;\n    const other = incoming ? inv.from : inv.to;\n    const g = GAMES[inv.game];\n    openModal(\n      h('div', { class: 'big' }, other.avatar),\n      incoming\n        ? h('div', {}, h('h2', {}, `${other.pseudo} te défie !`), h('p', { class: 'muted' }, `${g.icon} ${g.name}`))\n        : h('div', {}, h('h2', {}, `En attente de ${other.pseudo}…`), h('p', { class: 'muted' }, `Invitation envoyée : ${g.icon} ${g.name}`)),\n      h('div', { class: 'bar' }, h('i', { id: 'invite-bar' })),\n      h('div', { class: 'actions' }, incoming\n        ? [h('button', { class: 'btn good', on: { click: () => emit('invite:respond', { id: inv.id, accept: true }) } }, 'Accepter'),\n           h('button', { class: 'btn danger', on: { click: () => emit('invite:respond', { id: inv.id, accept: false }) } }, 'Refuser')]\n        : h('button', { class: 'btn', on: { click: () => emit('invite:cancel', { id: inv.id }) } }, 'Annuler')),\n    );\n    $('#modal').classList.add('center');\n  }\n  function onInviteEnded({ id, reason }) {\n    const inv = state.invite;\n    if (!inv || inv.id !== id) return;\n    state.invite = null;\n    closeModal();\n    if (reason === 'accepted') return;\n    const iSent = inv.from.id === state.me.id;\n    const other = iSent ? inv.to : inv.from;\n    const msgs = {\n      declined: `${other.pseudo} a refusé le défi.`,\n      expired: iSent ? `${other.pseudo} n'a pas répondu à temps.` : `L'invitation de ${other.pseudo} a expiré.`,\n      cancelled: iSent ? null : `${other.pseudo} a annulé son invitation.`,\n      unavailable: `${other.pseudo} n'est plus disponible.`,\n    };\n    if (msgs[reason]) toast(msgs[reason]);\n  }\n\n  /* ---------------- Salon ---------------- */\n\n  function statsRows(stats) {\n    const cell = (b) => (b ? `${b.w} · ${b.d} · ${b.l}` : '0 · 0 · 0');\n    return GAME_IDS.map((g) => {\n      const s = (stats && stats[g]) || {};\n      return h('tr', {}, h('th', {}, `${GAMES[g].icon} ${GAMES[g].name}`), h('td', {}, cell(s.human)), h('td', {}, cell(s.cpu)));\n    });\n  }\n  function renderMe() {\n    const me = state.me;\n    $('#me-card').replaceChildren(\n      h('div', { class: 'me-head' },\n        h('button', { class: 'big-avatar', title: \"Changer d'avatar\", 'aria-label': \"Changer d'avatar\", on: { click: openAvatarModal } }, me.avatar),\n        h('div', {}, h('div', { class: 'me-name' }, me.pseudo), h('div', { class: 'muted small' }, 'Ton profil'))),\n      h('table', { class: 'stats' },\n        h('thead', {}, h('tr', {}, h('th', {}, 'Victoires · nuls · défaites'), h('th', {}, 'Joueurs'), h('th', {}, 'Ordi'))),\n        h('tbody', {}, statsRows(me.stats))));\n  }\n  async function openAvatarModal() {\n    let avatars = [];\n    try { avatars = (await (await fetch('/api/config')).json()).avatars || []; } catch { return; }\n    const box = h('div', { class: 'avatars' });\n    renderAvatarPicker(box, avatars, async (a) => { closeModal(); await emit('profile:avatar', { avatar: a }); });\n    markAvatar(box, state.me.avatar);\n    openModal(h('h2', {}, 'Choisis ton avatar'), box, h('div', { class: 'actions' }, h('button', { class: 'btn', on: { click: closeModal } }, 'Fermer')));\n  }\n  function chooseGameFor(p) {\n    openModal(h('h2', {}, `Défier ${p.pseudo}`), h('p', { class: 'muted' }, 'Choisis le jeu :'),\n      h('div', { class: 'picklist' }, GAME_IDS.map((g) =>\n        h('button', { class: 'btn', on: { click: () => { closeModal(); emit('lobby:challenge', { targetId: p.id, game: g }); } } }, h('span', {}, GAMES[g].icon), GAMES[g].name))),\n      h('div', { class: 'actions' }, h('button', { class: 'btn', on: { click: closeModal } }, 'Annuler')));\n  }\n  function renderPlayers() {\n    const q = state.search.trim().toLowerCase();\n    const players = state.lobby.players.filter((p) => p.id !== state.me.id && p.pseudo.toLowerCase().includes(q));\n    $('#online-count').textContent = `${state.lobby.online} en ligne`;\n    $('#players').replaceChildren(...players.map((p) =>\n      h('li', { class: 'player' }, h('span', { class: 'av' }, p.avatar), h('span', { class: 'nm' }, p.pseudo),\n        h('button', { class: 'btn small primary', on: { click: () => chooseGameFor(p) } }, 'Défier'))));\n    const empty = $('#players-empty');\n    empty.hidden = players.length > 0;\n    empty.textContent = q ? 'Aucun joueur libre ne correspond à ta recherche.' : \"Personne d'autre n'est libre pour l'instant. Partage le lien du site à tes amis !\";\n  }\n  function renderCpuGames() {\n    $('#cpu-game').replaceChildren(...GAME_IDS.map((g) =>\n      h('button', { class: 'gbtn', 'aria-pressed': String(state.cpuGame === g), on: { click: () => { state.cpuGame = g; renderCpuGames(); } } },\n        h('span', { class: 'ic' }, GAMES[g].icon), GAMES[g].name)));\n  }\n  function initLobbyControls() {\n    $('#search').addEventListener('input', (e) => { state.search = e.target.value; renderPlayers(); });\n    for (const b of $$('#cpu-levels .level')) b.addEventListener('click', () => emit('cpu:start', { game: state.cpuGame, level: Number(b.dataset.level) }));\n    $('#cpu-rules').addEventListener('click', () => showRules(state.cpuGame));\n    $('#logout').addEventListener('click', async () => {\n      try { await api('/api/logout'); } catch { /* déconnexion locale quand même */ }\n      logoutLocal();\n    });\n    window.addEventListener('beforeinstallprompt', (e) => {\n      e.preventDefault(); state.installEvent = e; $('#install').hidden = false;\n    });\n    $('#install').addEventListener('click', async () => {\n      const e = state.installEvent; if (!e) return;\n      e.prompt(); try { await e.userChoice; } catch { /* ignoré */ }\n      state.installEvent = null; $('#install').hidden = true;\n    });\n    window.addEventListener('appinstalled', () => { $('#install').hidden = true; });\n  }\n\n  /* ---------------- Partie : en-tête et fin ---------------- */\n\n  const fmt = (ms) => { const s = Math.ceil(ms / 1000); return s >= 60 ? `${Math.floor(s / 60)} min ${String(s % 60).padStart(2, '0')} s` : `${s} s`; };\n  const isChessWhite = (g) => g.you === g.starter;\n\n  function tokenFor(g, idx) {\n    if (g.type === 'p4') return h('span', { class: `token t${idx}` });\n    if (g.type === 'ludo') return h('span', { class: `token t${idx}` });\n    if (g.type === 'dames' || g.type === 'echecs') return h('span', { class: `token ${idx === g.starter ? 'white' : 'black'}` });\n    return null;\n  }\n  function isTurnGame(g) { return g.type !== 'rps'; }\n  function playerBox(g, idx, right) {\n    const p = g.players[idx];\n    const active = !g.over && isTurnGame(g) && g.turn === idx;\n    let sub = idx === g.you ? 'Toi' : g.vsCpu ? `Niveau ${g.level}` : '';\n    if (idx !== g.you && !g.vsCpu) {\n      if (g.opponentLeft) sub = 'A quitté';\n      else if (!g.opponentConnected) sub = 'Déconnecté…';\n    }\n    const tk = tokenFor(g, idx);\n    return h('div', { class: `gp ${right ? 'right' : ''} ${active ? 'active' : ''}` }, h('span', { class: 'av' }, p.avatar),\n      h('div', { class: 'info' }, h('div', { class: 'nm' }, p.pseudo), h('div', { class: 'sub' }, tk ? [tk, ' ', sub] : sub)));\n  }\n  function statusText(g) {\n    if (g.over) return '';\n    if (g.type === 'rps') {\n      if (g.youChose) return g.vsCpu ? '…' : `En attente de ${g.players[1 - g.you].pseudo}…`;\n      return `Manche ${g.round} : fais ton choix !`;\n    }\n    const mine = g.turn === g.you;\n    const wait = g.vsCpu ? \"L'ordinateur réfléchit…\" : `Tour de ${g.players[g.turn].pseudo}`;\n    if (g.type === 'ludo') {\n      if (mine) return g.dice === null ? 'À toi : lance le dé !' : g.movable.length > 1 ? 'Choisis un pion à déplacer' : 'Déplace ton pion';\n      return g.vsCpu ? \"L'ordinateur joue…\" : wait;\n    }\n    if (g.type === 'echecs' && mine && g.check >= 0) return 'Échec ! À toi de jouer';\n    if (g.type === 'dames' && mine && g.mustCapture) return 'Prise obligatoire !';\n    return mine ? 'À toi de jouer !' : wait;\n  }\n\n  function renderGame() {\n    const g = state.game;\n    const opp = 1 - g.you;\n    const info = GAMES[g.type];\n    const board = { p4: renderP4, rps: renderRps, dames: renderDames, echecs: renderChess, ludo: renderLudo }[g.type](g);\n    const parts = [\n      h('div', { class: 'game-title' }, h('h2', {}, `${info.icon} ${info.name}`), h('button', { class: 'linkbtn', on: { click: () => showRules(g.type) } }, 'Règles')),\n      h('div', { class: 'game-head' }, playerBox(g, 0, false), h('div', { class: 'vs' }, 'VS'), playerBox(g, 1, true)),\n      h('div', { class: 'status', id: 'status' }, statusText(g), h('span', { class: 'timer', id: 'timer' })),\n      board,\n    ];\n    if (g.over) {\n      const won = g.winner === g.you, draw = g.winner === 'draw';\n      let text = draw ? 'Match nul !' : won ? 'Victoire ! 🎉' : `${g.players[opp].pseudo} a gagné`;\n      if (g.reason === 'forfeit') text = won ? `${g.players[opp].pseudo} a abandonné. Victoire !` : 'Tu as abandonné la partie.';\n      const extra = REASONS[g.reason] && g.reason !== 'forfeit' ? ` — ${REASONS[g.reason]}` : '';\n      parts.push(h('div', { class: `banner ${draw ? '' : won ? 'win' : 'lose'}` }, text + (draw ? extra : extra && g.reason === 'checkmate' ? extra : '')));\n      const actions = [];\n      if (g.vsCpu) {\n        actions.push(h('button', { class: 'btn primary', on: { click: () => emit('game:replay', {}) } }, 'Rejouer'));\n        if (g.level < 3) actions.push(h('button', { class: 'btn', on: { click: () => emit('game:replay', { level: g.level + 1 }) } }, `Niveau ${g.level + 1}`));\n      } else if (!g.opponentLeft) {\n        actions.push(h('button', { class: 'btn primary', disabled: g.rematch.you, on: { click: () => emit('game:rematch', { gameId: g.id }) } }, g.rematch.you ? 'Revanche demandée…' : 'Revanche'));\n      }\n      actions.push(h('button', { class: 'btn', on: { click: () => leave(true) } }, 'Retour au salon'));\n      parts.push(h('div', { class: 'game-actions' }, actions));\n      if (g.rematch.opponent && !g.rematch.you) parts.push(h('div', { class: 'notice' }, `${g.players[opp].pseudo} propose une revanche !`));\n    } else {\n      parts.push(h('div', { class: 'game-actions' }, h('button', { class: 'btn small danger', on: { click: () => leave(false) } }, g.vsCpu ? 'Quitter' : 'Abandonner')));\n      if (!g.vsCpu && !g.opponentConnected && !g.opponentLeft) parts.push(h('div', { class: 'notice' }, 'Ton adversaire est déconnecté. Il a quelques secondes pour revenir.'));\n    }\n    $('#game').replaceChildren(...parts);\n    tickTimer();\n  }\n\n  /** `quiet` : quitter sans demander (partie finie, contre l'ordinateur, ou déjà confirmé). */\n  async function leave(quiet) {\n    const g = state.game;\n    if (g && !quiet && !g.over && !g.vsCpu) return askLeave();\n    state.game = null; state.sel = null;\n    await emit('game:leave', {});\n    renderAll();\n  }\n\n  const move = (payload) => emit('game:move', { gameId: state.game.id, ...payload });\n\n  /* ---------------- Puissance 4 ---------------- */\n  function renderP4(g) {\n    const winCells = new Set((g.winLine || []).map(([r, c]) => `${r},${c}`));\n    const myTurn = !g.over && g.turn === g.you;\n    const cols = [];\n    for (let c = 0; c < 7; c++) {\n      const cells = [];\n      for (let r = 0; r < 6; r++) {\n        const v = g.board[r][c];\n        const cls = ['cell'];\n        if (v) cls.push(`p${v}`);\n        if (g.lastMove && g.lastMove.r === r && g.lastMove.c === c) cls.push('last');\n        if (winCells.has(`${r},${c}`)) cls.push('win');\n        cells.push(h('div', { class: cls.join(' ') }));\n      }\n      const can = myTurn && g.board[0][c] === 0;\n      cols.push(h('button', { class: `colbtn ${can ? 'can' : ''}`, disabled: !can, 'aria-label': `Colonne ${c + 1}`, on: { click: () => move({ col: c }) } }, cells));\n    }\n    return h('div', { class: 'board4' }, cols);\n  }\n\n  /* ---------------- Pierre-Feuille-Ciseaux ---------------- */\n  function renderRps(g) {\n    const last = g.lastRound;\n    const nodes = [h('div', { class: 'rps-scores' }, h('span', {}, String(g.scores[0])), h('small', {}, `premier à ${g.target}`), h('span', {}, String(g.scores[1])))];\n    if (last) {\n      const [a, b] = last.choices; const res = last.result;\n      nodes.push(h('div', { class: 'rps-reveal', 'aria-live': 'polite' },\n        h('div', { class: 'who2' }, h('span', { class: res === 0 ? 'win' : '' }, EMOJI[a]), g.players[0].pseudo),\n        h('div', { class: 'vs' }, res === 'tie' ? 'Égalité' : res === g.you ? '✓' : '✗'),\n        h('div', { class: 'who2' }, h('span', { class: res === 1 ? 'win' : '' }, EMOJI[b]), g.players[1].pseudo)));\n    } else nodes.push(h('div', { class: 'rps-reveal' }, '❔'));\n    if (!g.over) {\n      nodes.push(h('div', { class: 'rps-choices' }, ['pierre', 'feuille', 'ciseaux'].map((m) =>\n        h('button', { class: `rps-btn ${g.youChose === m ? 'chosen' : ''}`, disabled: !!g.youChose, on: { click: () => move({ choice: m }) } },\n          h('span', { class: 'em' }, EMOJI[m]), LABEL[m]))));\n    }\n    return h('div', {}, nodes);\n  }\n\n  /* ---------------- Échecs ---------------- */\n  function renderChess(g) {\n    const white = isChessWhite(g);\n    const myTurn = !g.over && g.turn === g.you;\n    const from = new Set(), targets = new Map();\n    if (myTurn) for (const [f, t, pr] of g.legal) { from.add(f); if (f === state.sel) targets.set(t, pr); }\n    const sqs = [];\n    for (let vr = 0; vr < 8; vr++) {\n      for (let vc = 0; vc < 8; vc++) {\n        const r = white ? vr : 7 - vr, c = white ? vc : 7 - vc, sq = r * 8 + c, v = g.board[sq];\n        const cls = ['sq', (r + c) % 2 ? 'dark' : ''];\n        if (state.sel === sq) cls.push('sel');\n        else if (g.last && (g.last.from === sq || g.last.to === sq)) cls.push('last');\n        if (g.check === sq) cls.push('check');\n        if (targets.has(sq)) cls.push('tgt', v ? 'cap' : '');\n        const clickable = myTurn && (from.has(sq) || targets.has(sq));\n        if (clickable) cls.push('clickable');\n        sqs.push(h('button', { class: cls.join(' '), 'aria-label': `Case ${'abcdefgh'[c]}${8 - r}`, tabIndex: clickable ? 0 : -1, on: { click: () => chessClick(g, sq, targets, from) } },\n          v ? h('span', { class: `pc ${v > 0 ? 'w' : 'b'}` }, CHESS[Math.abs(v)] + VS) : null));\n      }\n    }\n    return h('div', { class: 'chess' }, sqs);\n  }\n  function chessClick(g, sq, targets, from) {\n    if (g.over || g.turn !== g.you) return;\n    const rc = (i) => [i >> 3, i & 7];\n    if (targets.has(sq)) {\n      const f = state.sel;\n      if (targets.get(sq)) { // promotion : on demande la pièce\n        const mk = (code, glyph) => h('button', { 'aria-label': code, on: { click: () => { closeModal(); move({ from: rc(f), to: rc(sq), promo: code }); } } }, glyph + VS);\n        openModal(h('h2', {}, 'Promotion'), h('p', { class: 'muted' }, 'Choisis la nouvelle pièce :'),\n          h('div', { class: 'promo' }, [mk('q', '♛'), mk('r', '♜'), mk('b', '♝'), mk('n', '♞')]));\n        return;\n      }\n      state.sel = null;\n      return move({ from: rc(f), to: rc(sq) });\n    }\n    state.sel = from.has(sq) && state.sel !== sq ? sq : null;\n    renderGame();\n  }\n\n  /* ---------------- Dames (10 × 10) ---------------- */\n  function renderDames(g) {\n    const white = g.you === g.starter;\n    const myTurn = !g.over && g.turn === g.you;\n    const from = new Set(), targets = new Set();\n    if (myTurn) for (const [f, t] of g.legal) { from.add(f); if (f === state.sel) targets.add(t); }\n    const sqs = [];\n    for (let vr = 0; vr < 10; vr++) {\n      for (let vc = 0; vc < 10; vc++) {\n        const r = white ? vr : 9 - vr, c = white ? vc : 9 - vc, i = r * 10 + c, v = g.board[i];\n        const dark = (r + c) % 2 === 1;\n        const cls = ['sq', dark ? 'dark' : ''];\n        if (state.sel === i) cls.push('sel');\n        else if (g.last && (g.last.from === i || g.last.to === i)) cls.push('last');\n        if (targets.has(i)) cls.push('tgt');\n        const clickable = myTurn && (from.has(i) || targets.has(i));\n        if (clickable) cls.push('clickable');\n        sqs.push(h('button', { class: cls.join(' '), 'aria-label': `Case ${r + 1},${c + 1}`, tabIndex: clickable ? 0 : -1, on: { click: () => damesClick(g, i, targets, from) } },\n          v ? h('span', { class: `dm ${v > 0 ? 'w' : 'b'}` }, Math.abs(v) === 2 ? '♛' + VS : '') : null));\n      }\n    }\n    return h('div', { class: 'draughts' }, sqs);\n  }\n  function damesClick(g, i, targets, from) {\n    if (g.over || g.turn !== g.you) return;\n    const rc = (k) => [Math.floor(k / 10), k % 10];\n    if (targets.has(i)) { const f = state.sel; state.sel = null; return move({ from: rc(f), to: rc(i) }); }\n    state.sel = from.has(i) && state.sel !== i ? i : null;\n    renderGame();\n  }\n\n  /* ---------------- Ludo ---------------- */\n  const PATH = [[6,1],[6,2],[6,3],[6,4],[6,5],[5,6],[4,6],[3,6],[2,6],[1,6],[0,6],[0,7],[0,8],[1,8],[2,8],[3,8],[4,8],[5,8],[6,9],[6,10],[6,11],[6,12],[6,13],[6,14],[7,14],[8,14],[8,13],[8,12],[8,11],[8,10],[8,9],[9,8],[10,8],[11,8],[12,8],[13,8],[14,8],[14,7],[14,6],[13,6],[12,6],[11,6],[10,6],[9,6],[8,5],[8,4],[8,3],[8,2],[8,1],[8,0],[7,0],[6,0]];\n  const LSTART = [0, 26];\n  const LSAFE = new Set([0, 8, 13, 21, 26, 34, 39, 47]);\n  const HOMECOL = [[[7,1],[7,2],[7,3],[7,4],[7,5]], [[7,13],[7,12],[7,11],[7,10],[7,9]]];\n  const FINISH = [[7, 6], [7, 8]];\n  const YARD = [[[1,1],[1,4],[4,1],[4,4]], [[10,10],[10,13],[13,10],[13,13]]];\n  function ludoCell(idx, p, k) {\n    if (p === -1) return YARD[idx][k];\n    if (p <= 50) return PATH[(LSTART[idx] + p) % 52];\n    if (p <= 55) return HOMECOL[idx][p - 51];\n    return FINISH[idx];\n  }\n  function renderLudo(g) {\n    const myTurn = !g.over && g.turn === g.you;\n    const cells = [];\n    const g1 = (r, c) => [r + 1, c + 1];\n    cells.push(h('div', { class: 'yard y0', grid: ['1 / span 6', '1 / span 6'] }), h('div', { class: 'yard yx', grid: ['1 / span 6', '10 / span 6'] }),\n      h('div', { class: 'yard yx', grid: ['10 / span 6', '1 / span 6'] }), h('div', { class: 'yard y1', grid: ['10 / span 6', '10 / span 6'] }));\n    for (const idx of [0, 1]) for (const [r, c] of YARD[idx]) cells.push(h('div', { class: 'slot', grid: g1(r, c) }));\n    PATH.forEach(([r, c], i) => {\n      const cls = ['tk']; if (i === LSTART[0]) cls.push('s0'); if (i === LSTART[1]) cls.push('s1');\n      cells.push(h('div', { class: cls.join(' '), grid: g1(r, c) }, LSAFE.has(i) ? '★' : ''));\n    });\n    HOMECOL[0].forEach(([r, c]) => cells.push(h('div', { class: 'hc0', grid: g1(r, c) })));\n    HOMECOL[1].forEach(([r, c]) => cells.push(h('div', { class: 'hc1', grid: g1(r, c) })));\n    cells.push(h('div', { class: 'centerbox', grid: ['7 / span 3', '7 / span 3'] }, '🏠'));\n\n    // Pions : regroupés par case pour décaler ceux qui se chevauchent\n    const groups = new Map();\n    const pawns = [];\n    for (const idx of [0, 1]) g.pawns[idx].forEach((p, k) => {\n      const [r, c] = ludoCell(idx, p, k);\n      const key = `${r},${c}`;\n      if (!groups.has(key)) groups.set(key, []);\n      const rec = { idx, k, p, r, c };\n      groups.get(key).push(rec); pawns.push(rec);\n    });\n    for (const rec of pawns) {\n      const can = myTurn && rec.idx === g.you && g.dice !== null && g.movable.includes(rec.k);\n      const grp = groups.get(`${rec.r},${rec.c}`);\n      const el = h('button', {\n        class: `pawn p${rec.idx} ${can ? 'can' : ''}`, disabled: !can, 'aria-label': `Pion ${rec.k + 1} de ${g.players[rec.idx].pseudo}`,\n        grid: g1(rec.r, rec.c), on: { click: () => move({ pawn: rec.k }) },\n      }, String(rec.k + 1));\n      if (grp.length > 1) {\n        const n = grp.indexOf(rec);\n        el.style.transform = `translate(${((n % 3) - 1) * 28}%, ${(Math.floor(n / 3) - 0.5) * 36}%) scale(.72)`;\n      }\n      cells.push(el);\n    }\n    const boardEl = h('div', { class: 'ludo' }, cells);\n\n    // Dé et choix de pion\n    const dieVal = g.dice !== null ? g.dice : g.lastRoll ? g.lastRoll.v : 0;\n    const dieEl = h('div', { class: `die ${state.rolling ? 'rolling' : ''}`, 'aria-label': dieVal ? `Dé : ${dieVal}` : 'Dé' }, dieVal ? DIE[dieVal] + VS : '🎲');\n    const rollBtn = myTurn && g.dice === null\n      ? h('button', { class: 'btn primary', on: { click: () => move({ action: 'roll' }) } }, '🎲 Lancer le dé')\n      : null;\n    let msg = '';\n    const lm = g.lastMove, lr = g.lastRoll;\n    if (lr && lr.note === 'none') msg = `${g.players[lr.by].pseudo} a fait ${lr.v} : aucun pion ne peut bouger.`;\n    else if (lm && g.dice === null) {\n      const who = g.players[lm.by].pseudo;\n      msg = lm.captured ? `${who} capture ${lm.captured} pion${lm.captured > 1 ? 's' : ''} !` : lm.to === 56 ? `${who} met un pion à la maison !` : '';\n    }\n    const picks = myTurn && g.dice !== null && g.movable.length > 1\n      ? h('div', { class: 'pawnpick' }, g.movable.map((k) => h('button', { class: 'btn small', on: { click: () => move({ pawn: k }) } }, `Pion ${k + 1}`))) : null;\n    const home = (i) => g.pawns[i].filter((p) => p === 56).length;\n    return h('div', {}, boardEl,\n      h('div', { class: 'dice-zone' }, dieEl, rollBtn),\n      msg ? h('div', { class: 'notice' }, msg) : null, picks,\n      h('div', { class: 'legend' }, h('span', {}, `${g.players[0].pseudo} : ${home(0)}/4 à la maison`), h('span', {}, `${g.players[1].pseudo} : ${home(1)}/4 à la maison`), h('span', {}, '★ case protégée')));\n  }\n\n  /* ---------------- Compteurs et affichage ---------------- */\n  function tickTimer() {\n    const g = state.game, t = $('#timer');\n    if (g && t && !g.over && state.gameDeadline) {\n      const left = Math.max(0, state.gameDeadline - Date.now());\n      t.textContent = `(${fmt(left)})`;\n      t.classList.toggle('low', left <= 5000);\n    } else if (t) t.textContent = '';\n    const bar = $('#invite-bar');\n    if (bar && state.invite) bar.style.transform = `scaleX(${Math.max(0, (state.inviteDeadline - Date.now()) / Math.max(1, state.invite.timeLeft))})`;\n  }\n  function renderAll() {\n    if (!state.me) return showScreen('auth');\n    $('#who').textContent = state.me.pseudo;\n    if (state.game) { showScreen('game'); renderGame(); }\n    else { showScreen('lobby'); renderMe(); renderCpuGames(); renderPlayers(); }\n    window.scrollTo(0, 0);\n  }\n\n  async function start() {\n    initHistory();\n    await initAuthScreen();\n    initLobbyControls();\n    setInterval(tickTimer, 250);\n    $('#overlay').addEventListener('click', (e) => { if (e.target === $('#overlay') && !state.invite) closeModal(); });\n    if (state.token) {\n      state.me = { id: '', pseudo: '', avatar: '', stats: emptyStats() };\n      connect();\n    } else showScreen('auth');\n  }\n  start();\n})();\n\nif ('serviceWorker' in navigator) {\n  window.addEventListener('load', () => navigator.serviceWorker.register('/sw.js').catch(() => {}));\n}\n</script>\n</body>\n</html>\n";

/* ================================================================== */
/* Serveur HTTP + temps réel                                           */
/* ================================================================== */

const LEVELS = [1, 2, 3];
const TURN_GAMES = { dames: Dames, echecs: Chess, ludo: Ludo }; // jeux au tour par tour gérés de façon générique
const GAME_LABEL = { p4: 'Puissance 4', rps: 'Pierre-Feuille-Ciseaux', dames: 'Dames', echecs: 'Échecs', ludo: 'Ludo' };

const num = (...vals) => {
  for (const v of vals) if (v != null && v !== '' && Number.isFinite(Number(v))) return Number(v);
  return undefined;
};
const rid = () => crypto.randomBytes(6).toString('hex');
const isObj = (x) => x !== null && typeof x === 'object' && !Array.isArray(x);

function createApp(opts = {}) {
  // Les dépendances sont chargées ici (et non en haut du fichier) pour pouvoir tester les règles sans les installer.
  const express = require('express');
  const { Server } = require('socket.io');

  const cfg = {
    dataFile: opts.dataFile || process.env.DATA_FILE || path.join(__dirname, 'data', 'db.json'),
    databaseUrl: opts.databaseUrl !== undefined ? opts.databaseUrl : process.env.DATABASE_URL || null,
    inviteMs: num(opts.inviteMs, process.env.INVITE_MS, 30000), // durée de validité d'une invitation
    p4TurnMs: num(opts.p4TurnMs, process.env.P4_TURN_MS, 30000), // temps par coup (Puissance 4 entre humains)
    rpsRoundMs: num(opts.rpsRoundMs, process.env.RPS_ROUND_MS, 15000), // temps par manche (PFC entre humains)
    turnMs: Object.assign({ dames: 60000, echecs: 120000, ludo: 40000 }, opts.turnMs), // temps par action (autres jeux)
    graceMs: num(opts.graceMs, process.env.GRACE_MS, 30000), // délai de reconnexion en pleine partie
    cpuDelayMs: num(opts.cpuDelayMs, process.env.CPU_DELAY_MS, 700), // "temps de réflexion" de l'ordinateur
    authLimit: num(opts.authLimit, process.env.AUTH_LIMIT, 30), // tentatives d'inscription/connexion / 10 min / IP
  };

  const store = new Store(cfg.dataFile, { databaseUrl: cfg.databaseUrl });
  const app = express();
  const server = http.createServer(app);
  const io = new Server(server, { pingInterval: 10000, pingTimeout: 8000 });

  /* ================================================================ */
  /* HTTP : page, application installable, API de comptes              */
  /* ================================================================ */

  // La page web est intégrée à ce fichier (EMBEDDED_HTML, ajouté à l'assemblage) : aucun autre fichier n'est nécessaire.
  const htmlPath = opts.htmlPath || [path.join(__dirname, 'index.html'), path.join(__dirname, 'public', 'index.html')].find((f) => fs.existsSync(f));
  const indexHtml = typeof EMBEDDED_HTML === 'string' ? EMBEDDED_HTML : htmlPath ? fs.readFileSync(htmlPath, 'utf8') : '<!doctype html><meta charset="utf-8"><p>Page introuvable.</p>';

  // La page contient son CSS et son JavaScript : on les autorise par empreinte (hash), tout le reste reste bloqué.
  const inlineHashes = (tag) => {
    const re = new RegExp(`<${tag}(?![^>]*\\bsrc=)[^>]*>([\\s\\S]*?)</${tag}>`, 'gi');
    const out = [];
    let m;
    while ((m = re.exec(indexHtml))) out.push(`'sha256-${crypto.createHash('sha256').update(m[1]).digest('base64')}'`);
    return out;
  };
  const csp = [
    "default-src 'self'",
    "connect-src 'self' ws: wss:",
    "img-src 'self' data:",
    `style-src 'self' ${inlineHashes('style').join(' ')}`.trim(),
    `script-src 'self' ${inlineHashes('script').join(' ')}`.trim(),
    "manifest-src 'self'",
    "worker-src 'self'",
    "base-uri 'none'",
    "form-action 'self'",
    "frame-ancestors 'none'",
  ].join('; ');

  app.set('trust proxy', 1);
  app.disable('x-powered-by');
  app.use((req, res, next) => {
    res.setHeader('X-Content-Type-Options', 'nosniff');
    res.setHeader('X-Frame-Options', 'DENY');
    res.setHeader('Referrer-Policy', 'same-origin');
    res.setHeader('Content-Security-Policy', csp);
    next();
  });
  app.use(express.json({ limit: '10kb' }));

  const sendIndex = (req, res) => {
    res.setHeader('Cache-Control', 'no-cache');
    res.type('html').send(indexHtml);
  };
  app.get('/', sendIndex);
  app.get('/index.html', sendIndex);
  app.get('/manifest.webmanifest', (req, res) => res.type('application/manifest+json').send(JSON.stringify(MANIFEST)));
  app.get('/sw.js', (req, res) => {
    res.setHeader('Cache-Control', 'no-cache');
    res.type('application/javascript').send(SERVICE_WORKER);
  });
  const sendIcon = (name) => (req, res, next) => {
    const icon = ICONS[name || req.params.name];
    if (!icon) return next();
    res.setHeader('Cache-Control', 'public, max-age=86400');
    res.type('image/png').send(icon);
  };
  app.get('/icons/:name', sendIcon());
  app.get('/apple-touch-icon.png', sendIcon('apple-touch-icon.png'));

  const hits = new Map();
  const rateOk = (key, max, windowMs) => {
    const now = Date.now();
    let e = hits.get(key);
    if (!e || e.reset < now) {
      e = { n: 0, reset: now + windowMs };
      hits.set(key, e);
    }
    e.n++;
    return e.n <= max;
  };
  const hitsTimer = setInterval(() => {
    const now = Date.now();
    for (const [k, e] of hits) if (e.reset < now) hits.delete(k);
  }, 60000);
  hitsTimer.unref();

  const bearer = (req) => {
    const m = /^Bearer ([a-f0-9]{64})$/.exec(req.headers.authorization || '');
    return m ? m[1] : null;
  };
  const selfView = (u) => ({ id: u.id, pseudo: u.pseudo, avatar: u.avatar, stats: u.stats });
  const tooMany = (res) => res.status(429).json({ error: 'Trop de tentatives. Réessaie dans quelques minutes.' });

  app.get('/healthz', (req, res) => res.type('text').send(`ok · stockage : ${store.mode} · ${Object.keys(store.users).length} compte(s)`));
  app.get('/api/config', (req, res) => res.json({ avatars: AVATARS, persistent: store.mode === 'postgres' }));

  app.post('/api/register', async (req, res) => {
    try {
      if (!rateOk(`auth:${req.ip}`, cfg.authLimit, 10 * 60 * 1000)) return tooMany(res);
      const v = validateRegistration(req.body);
      if (v.error) return res.status(400).json({ error: v.error, field: v.field });
      if (store.emailTaken(v.email)) return res.status(409).json({ error: 'Cette adresse e-mail est déjà utilisée.', field: 'email' });
      if (store.pseudoTaken(v.pseudo)) return res.status(409).json({ error: 'Ce pseudo est déjà pris.', field: 'pseudo' });
      const user = await store.createUser(v);
      res.json({ token: store.createSession(user.id), me: selfView(user) });
    } catch (e) {
      if (e.code === 'EMAIL_TAKEN') return res.status(409).json({ error: 'Cette adresse e-mail est déjà utilisée.', field: 'email' });
      if (e.code === 'PSEUDO_TAKEN') return res.status(409).json({ error: 'Ce pseudo est déjà pris.', field: 'pseudo' });
      console.error('[register]', e);
      res.status(500).json({ error: 'Erreur serveur.' });
    }
  });

  app.post('/api/login', async (req, res) => {
    try {
      if (!rateOk(`auth:${req.ip}`, cfg.authLimit, 10 * 60 * 1000)) return tooMany(res);
      const b = isObj(req.body) ? req.body : {};
      const email = typeof b.email === 'string' ? b.email.trim().toLowerCase() : '';
      const password = typeof b.password === 'string' ? b.password.slice(0, 128) : '';
      const user = store.findByEmail(email);
      const ok = await store.verifyPassword(user, password);
      if (!ok) return res.status(401).json({ error: 'E-mail ou mot de passe incorrect.' });
      res.json({ token: store.createSession(user.id), me: selfView(user) });
    } catch (e) {
      console.error('[login]', e);
      res.status(500).json({ error: 'Erreur serveur.' });
    }
  });

  app.post('/api/logout', (req, res) => {
    const token = bearer(req);
    const user = token && store.getSession(token);
    if (token) store.deleteSession(token);
    if (user) {
      const rec = online.get(user.id);
      if (rec) {
        const sock = io.sockets.sockets.get(rec.socketId);
        if (sock) sock.disconnect(true);
        dropUser(user.id);
      }
    }
    res.json({ ok: true });
  });

  /* ================================================================ */
  /* État en mémoire                                                    */
  /* ================================================================ */

  // uid -> { uid, socketId, status: 'free' | 'reserved' | 'playing', gameId, inviteId, disconnected, graceTimer }
  const online = new Map();
  const invites = new Map(); // id -> { id, from, to, game, expires, timer }
  const games = new Map(); // id -> game
  const cpuMemory = new Map(); // uid -> historique des manches PFC contre l'ordinateur (pour qu'il "apprenne")

  const pub = (uid) => {
    const u = store.getUser(uid);
    return u ? { id: u.id, pseudo: u.pseudo, avatar: u.avatar } : null;
  };

  function emitTo(uid, event, payload) {
    const rec = online.get(uid);
    if (rec && !rec.disconnected) io.to(rec.socketId).emit(event, payload);
  }

  /* ---------------- Salon ---------------- */

  function lobbySnapshot() {
    const players = [];
    let count = 0;
    for (const rec of online.values()) {
      if (rec.disconnected) continue;
      count++;
      if (rec.status === 'free') players.push(pub(rec.uid));
    }
    players.sort((a, b) => a.pseudo.localeCompare(b.pseudo, 'fr', { sensitivity: 'base' }));
    return { players, online: count };
  }

  let lobbyTimer = null;
  function broadcastLobby() {
    if (lobbyTimer) return;
    lobbyTimer = setTimeout(() => {
      lobbyTimer = null;
      io.emit('lobby:update', lobbySnapshot());
    }, 50);
  }

  /* ---------------- Invitations ---------------- */

  const inviteView = (inv) => ({
    id: inv.id,
    game: inv.game,
    from: pub(inv.from),
    to: pub(inv.to),
    timeLeft: Math.max(0, inv.expires - Date.now()),
  });

  function endInvite(id, reason) {
    const inv = invites.get(id);
    if (!inv) return;
    clearTimeout(inv.timer);
    invites.delete(id);
    for (const uid of [inv.from, inv.to]) {
      const rec = online.get(uid);
      if (rec && rec.inviteId === id) {
        rec.inviteId = null;
        if (rec.status === 'reserved') rec.status = 'free';
      }
      emitTo(uid, 'invite:ended', { id, reason });
    }
    broadcastLobby();
  }

  function acceptInvite(inv) {
    clearTimeout(inv.timer);
    invites.delete(inv.id);
    for (const uid of [inv.from, inv.to]) {
      const rec = online.get(uid);
      if (rec) rec.inviteId = null;
      emitTo(uid, 'invite:ended', { id: inv.id, reason: 'accepted' });
    }
    const game = createGame({ type: inv.game, p0: inv.from, p1: inv.to, starter: randInt(2) });
    pushGame(game);
    broadcastLobby();
  }

  /* ---------------- Parties ---------------- */

  function newState(type, starter) {
    if (type === 'p4') return { board: C4.newBoard(), turn: starter, winLine: null, lastMove: null };
    if (type === 'rps') return { scores: [0, 0], round: 1, choices: [null, null], lastRound: null };
    return TURN_GAMES[type].init(starter);
  }

  function createGame({ type, p0, p1, level = null, starter = 0 }) {
    const vsCpu = p1 === null;
    const game = {
      id: rid(),
      type,
      vsCpu,
      level: vsCpu ? level : null,
      starter,
      players: [pub(p0), vsCpu ? { id: null, pseudo: 'Ordinateur', avatar: '🤖' } : pub(p1)],
      state: newState(type, starter),
      over: false,
      winner: null, // 0 | 1 | 'draw'
      reason: null, // 'win' | 'full' | 'forfeit' | 'checkmate' | 'stalemate' | …
      deadline: null,
      timer: null,
      cpuTimer: null,
      rematch: [false, false],
      left: [false, false],
    };
    games.set(game.id, game);
    for (const p of game.players) {
      const rec = p.id && online.get(p.id);
      if (rec) {
        rec.gameId = game.id;
        rec.status = 'playing';
      }
    }
    armGame(game);
    return game;
  }

  function clearTimers(game) {
    clearTimeout(game.timer);
    clearTimeout(game.cpuTimer);
    game.timer = game.cpuTimer = null;
    game.deadline = null;
  }

  function destroyGame(game) {
    clearTimers(game);
    games.delete(game.id);
  }

  function setDeadline(game, ms, fn) {
    game.deadline = Date.now() + ms;
    game.timer = setTimeout(() => {
      if (games.has(game.id) && !game.over) fn();
    }, ms);
  }

  /** Met en place ce que le jeu attend ensuite : coup de l'ordinateur ou compte à rebours d'un joueur. */
  function armGame(game) {
    clearTimers(game);
    if (game.over) return;
    if (game.type === 'p4') {
      if (game.vsCpu) {
        if (game.state.turn === 1) {
          game.cpuTimer = setTimeout(() => cpuPlay(game), cfg.cpuDelayMs + Math.random() * 400);
        }
      } else {
        setDeadline(game, cfg.p4TurnMs, () => p4Timeout(game));
      }
    } else if (game.type === 'rps') {
      if (!game.vsCpu) setDeadline(game, cfg.rpsRoundMs, () => rpsTimeout(game));
    } else if (game.vsCpu) {
      if (game.state.turn === 1) game.cpuTimer = setTimeout(() => turnCpu(game), cfg.cpuDelayMs + Math.random() * 400);
    } else {
      setDeadline(game, cfg.turnMs[game.type], () => turnTimeout(game));
    }
  }

  function gameView(game, uid) {
    const idx = game.players.findIndex((p) => p.id === uid);
    const other = game.players[1 - idx];
    const orec = other.id ? online.get(other.id) : null;
    const s = game.state;
    const view = {
      id: game.id,
      type: game.type,
      vsCpu: game.vsCpu,
      level: game.level,
      you: idx,
      players: game.players,
      starter: game.starter,
      over: game.over,
      winner: game.winner,
      reason: game.reason,
      timeLeft: game.deadline ? Math.max(0, game.deadline - Date.now()) : null,
      opponentConnected: game.vsCpu ? true : !!(orec && !orec.disconnected && orec.gameId === game.id),
      opponentLeft: game.left[1 - idx],
      rematch: { you: game.rematch[idx], opponent: game.rematch[1 - idx] },
    };
    if (game.type === 'p4') {
      Object.assign(view, { board: s.board, turn: s.turn, winLine: s.winLine, lastMove: s.lastMove });
    } else if (game.type === 'rps') {
      Object.assign(view, {
        scores: s.scores,
        round: s.round,
        target: RPS.TARGET,
        youChose: s.choices[idx],
        opponentChose: s.choices[1 - idx] !== null,
        lastRound: s.lastRound,
      });
    } else {
      Object.assign(view, TURN_GAMES[game.type].view(s));
    }
    return view;
  }

  function pushGame(game) {
    game.players.forEach((p, i) => {
      if (!p.id || game.left[i]) return;
      const rec = online.get(p.id);
      if (!rec || rec.gameId !== game.id) return;
      emitTo(p.id, 'game:state', gameView(game, p.id));
    });
  }

  function recordResult(game) {
    const bucket = game.vsCpu ? 'cpu' : 'human';
    game.players.forEach((p, i) => {
      const u = p.id && store.getUser(p.id);
      if (!u) return;
      const key = game.winner === 'draw' ? 'd' : game.winner === i ? 'w' : 'l';
      if (!u.stats[game.type]) u.stats[game.type] = emptyGameStats();
      u.stats[game.type][bucket][key]++;
    });
    store.save();
    for (const p of game.players) {
      const u = p.id && store.getUser(p.id);
      if (u) emitTo(p.id, 'me:update', { stats: u.stats });
    }
  }

  function finishGame(game, winner, reason) {
    clearTimers(game);
    game.over = true;
    game.winner = winner;
    game.reason = reason;
    recordResult(game);
    pushGame(game);
  }

  /** Un joueur quitte la partie (bouton, déconnexion prolongée, déconnexion du compte). */
  function leaveGame(uid) {
    const rec = online.get(uid);
    if (!rec || !rec.gameId) return;
    const game = games.get(rec.gameId);
    rec.gameId = null;
    if (rec.status === 'playing') rec.status = 'free';
    if (!game) return;
    if (game.vsCpu) return destroyGame(game);
    const idx = game.players.findIndex((p) => p.id === uid);
    game.left[idx] = true;
    if (!game.over) finishGame(game, 1 - idx, 'forfeit'); // abandonner = perdre
    if (game.left[0] && game.left[1]) destroyGame(game);
    else pushGame(game);
  }

  /* ---- Puissance 4 ---- */

  function p4Play(game, idx, col) {
    const s = game.state;
    if (s.turn !== idx) return "Ce n'est pas ton tour.";
    if (!Number.isInteger(col) || col < 0 || col >= C4.COLS) return 'Colonne invalide.';
    if (s.board[0][col] !== 0) return 'Cette colonne est pleine.';
    p4Apply(game, idx, col);
    return null;
  }

  function p4Apply(game, idx, col) {
    const s = game.state;
    const row = C4.drop(s.board, col, idx + 1);
    s.lastMove = { r: row, c: col, p: idx };
    const line = C4.lineAt(s.board, row, col);
    if (line) {
      s.winLine = line;
      return finishGame(game, idx, 'win');
    }
    if (C4.isFull(s.board)) return finishGame(game, 'draw', 'full');
    s.turn = 1 - idx;
    armGame(game);
    pushGame(game);
  }

  function p4Timeout(game) {
    // Temps écoulé : un coup au hasard est joué à la place du joueur.
    const moves = C4.validMoves(game.state.board);
    p4Apply(game, game.state.turn, moves[randInt(moves.length)]);
  }

  function cpuPlay(game) {
    if (!games.has(game.id) || game.over || game.type !== 'p4') return;
    const col = C4.cpuMove(game.state.board, game.level, 2);
    if (col >= 0) p4Apply(game, 1, col);
  }

  /* ---- Pierre-Feuille-Ciseaux ---- */

  function rpsChoose(game, idx, choice) {
    const s = game.state;
    if (!RPS.MOVES.includes(choice)) return 'Choix invalide.';
    if (s.choices[idx] !== null) return 'Tu as déjà choisi pour cette manche.';
    s.choices[idx] = choice;
    if (game.vsCpu) {
      // L'ordinateur décide d'après les manches PRÉcédentes uniquement.
      s.choices[1] = RPS.cpuChoice(game.level, cpuMemory.get(game.players[0].id) || []);
    }
    if (s.choices[0] !== null && s.choices[1] !== null) rpsResolve(game);
    else pushGame(game);
    return null;
  }

  function rpsResolve(game) {
    const s = game.state;
    const [a, b] = s.choices;
    const result = RPS.outcome(a, b);
    s.lastRound = { n: s.round, choices: [a, b], result };
    s.round++;
    s.choices = [null, null];
    if (result !== 'tie') s.scores[result]++;
    if (game.vsCpu) {
      const uid = game.players[0].id;
      const mem = cpuMemory.get(uid) || [];
      mem.push({ h: a, c: b, r: result === 'tie' ? 't' : result === 0 ? 'w' : 'l' });
      if (mem.length > 300) mem.shift();
      cpuMemory.set(uid, mem);
    }
    if (result !== 'tie' && s.scores[result] >= RPS.TARGET) return finishGame(game, result, 'win');
    armGame(game);
    pushGame(game);
  }

  function rpsTimeout(game) {
    // Temps écoulé : un choix au hasard est fait pour ceux qui n'ont pas joué.
    const s = game.state;
    for (let i = 0; i < 2; i++) if (s.choices[i] === null) s.choices[i] = RPS.MOVES[randInt(3)];
    rpsResolve(game);
  }

  /* ---- Dames, Échecs, Ludo (jeux au tour par tour) ---- */

  function afterTurnAction(game) {
    const r = game.state.result;
    if (r) return finishGame(game, r.winner, r.reason);
    armGame(game);
    pushGame(game);
  }

  function turnCpu(game) {
    if (!games.has(game.id) || game.over || !TURN_GAMES[game.type]) return;
    const mod = TURN_GAMES[game.type];
    const s = game.state;
    if (s.turn !== 1) return;
    let payload;
    try {
      payload = mod.cpu(s, game.level);
    } catch (e) {
      console.error(`[cpu ${game.type}]`, e);
      payload = mod.randomPayload(s);
    }
    let err = mod.play(s, 1, payload);
    if (err) {
      console.error(`[cpu ${game.type}] coup refusé :`, err, JSON.stringify(payload));
      err = mod.play(s, 1, mod.randomPayload(s));
    }
    afterTurnAction(game);
  }

  function turnTimeout(game) {
    // Temps écoulé : une action au hasard est jouée à la place du joueur.
    const mod = TURN_GAMES[game.type];
    const s = game.state;
    mod.play(s, s.turn, mod.randomPayload(s));
    afterTurnAction(game);
  }

  /* ================================================================ */
  /* Connexions temps réel                                              */
  /* ================================================================ */

  io.use((socket, next) => {
    const token = socket.handshake.auth && socket.handshake.auth.token;
    const user = store.getSession(token);
    if (!user) return next(new Error('unauthorized'));
    socket.data.uid = user.id;
    next();
  });

  function dropUser(uid) {
    const rec = online.get(uid);
    if (!rec) return;
    clearTimeout(rec.graceTimer);
    if (rec.inviteId) endInvite(rec.inviteId, 'unavailable');
    if (rec.gameId) leaveGame(uid);
    online.delete(uid);
    broadcastLobby();
  }

  function buildInit(uid) {
    const rec = online.get(uid);
    const game = rec.gameId ? games.get(rec.gameId) : null;
    const inv = rec.inviteId ? invites.get(rec.inviteId) : null;
    return {
      me: selfView(store.getUser(uid)),
      game: game ? gameView(game, uid) : null,
      invite: inv ? inviteView(inv) : null,
      lobby: lobbySnapshot(),
    };
  }

  io.on('connection', (socket) => {
    const uid = socket.data.uid;

    // Un seul appareil/onglet par compte : le plus récent remplace l'ancien.
    let rec = online.get(uid);
    if (rec) {
      if (!rec.disconnected && rec.socketId !== socket.id) {
        const old = io.sockets.sockets.get(rec.socketId);
        if (old) {
          old.emit('session:replaced');
          old.disconnect(true);
        }
      }
      clearTimeout(rec.graceTimer);
      rec.graceTimer = null;
      rec.disconnected = false;
      rec.socketId = socket.id;
    } else {
      rec = { uid, socketId: socket.id, status: 'free', gameId: null, inviteId: null, disconnected: false, graceTimer: null };
      online.set(uid, rec);
    }

    socket.emit('init', buildInit(uid));
    const game = rec.gameId && games.get(rec.gameId);
    if (game && !game.vsCpu) pushGame(game); // l'adversaire voit que tu es revenu
    broadcastLobby();

    // Garde-fou : pas plus de ~40 messages par seconde et par connexion.
    let windowStart = Date.now();
    let count = 0;
    socket.use((packet, next) => {
      const now = Date.now();
      if (now - windowStart > 1000) {
        windowStart = now;
        count = 0;
      }
      if (++count > 40) return next(new Error('Trop de requêtes.'));
      next();
    });

    const on = (event, handler) =>
      socket.on(event, (payload, ack) => {
        const reply = typeof ack === 'function' ? ack : () => {};
        try {
          handler(isObj(payload) ? payload : {}, reply);
        } catch (e) {
          console.error(`[${event}]`, e);
          reply({ ok: false, error: 'Erreur serveur.' });
        }
      });
    const fail = (reply, error) => reply({ ok: false, error });

    on('lobby:challenge', (p, reply) => {
      if (!GAME_TYPES.includes(p.game)) return fail(reply, 'Jeu inconnu.');
      const targetId = String(p.targetId || '');
      const me = online.get(uid);
      const target = online.get(targetId);
      if (!me || me.status !== 'free') return fail(reply, "Tu n'es pas disponible pour un défi.");
      if (targetId === uid) return fail(reply, 'Tu ne peux pas te défier toi-même.');
      if (!target || target.disconnected || target.status !== 'free') return fail(reply, "Ce joueur n'est plus disponible.");

      const inv = { id: rid(), from: uid, to: targetId, game: p.game, expires: Date.now() + cfg.inviteMs, timer: null };
      inv.timer = setTimeout(() => endInvite(inv.id, 'expired'), cfg.inviteMs);
      invites.set(inv.id, inv);
      // Pendant l'invitation, les deux joueurs sont "réservés" : ils disparaissent de la liste des libres.
      me.status = target.status = 'reserved';
      me.inviteId = target.inviteId = inv.id;
      const view = inviteView(inv);
      emitTo(uid, 'invite:new', view);
      emitTo(targetId, 'invite:new', view);
      broadcastLobby();
      reply({ ok: true });
    });

    on('invite:cancel', (p, reply) => {
      const inv = invites.get(String(p.id || ''));
      if (!inv || inv.from !== uid) return fail(reply, "Cette invitation n'est plus valide.");
      endInvite(inv.id, 'cancelled');
      reply({ ok: true });
    });

    on('invite:respond', (p, reply) => {
      const inv = invites.get(String(p.id || ''));
      if (!inv || inv.to !== uid) return fail(reply, "Cette invitation n'est plus valide.");
      if (p.accept === true) acceptInvite(inv);
      else endInvite(inv.id, 'declined');
      reply({ ok: true });
    });

    on('cpu:start', (p, reply) => {
      const me = online.get(uid);
      if (!me || me.status !== 'free') return fail(reply, "Tu n'es pas disponible.");
      if (!GAME_TYPES.includes(p.game) || !LEVELS.includes(p.level)) return fail(reply, 'Paramètres invalides.');
      const g = createGame({ type: p.game, p0: uid, p1: null, level: p.level, starter: 0 });
      pushGame(g);
      broadcastLobby();
      reply({ ok: true });
    });

    on('game:move', (p, reply) => {
      const me = online.get(uid);
      const g = games.get(String(p.gameId || ''));
      if (!me || !g || me.gameId !== g.id) return fail(reply, 'Partie introuvable.');
      if (g.over) return fail(reply, 'La partie est terminée.');
      const idx = g.players.findIndex((x) => x.id === uid);
      if (g.type === 'p4') {
        const err = p4Play(g, idx, p.col);
        return err ? fail(reply, err) : reply({ ok: true });
      }
      if (g.type === 'rps') {
        const err = rpsChoose(g, idx, p.choice);
        return err ? fail(reply, err) : reply({ ok: true });
      }
      const err = TURN_GAMES[g.type].play(g.state, idx, p);
      if (err) return fail(reply, err);
      afterTurnAction(g);
      reply({ ok: true });
    });

    on('game:leave', (p, reply) => {
      leaveGame(uid);
      broadcastLobby();
      reply({ ok: true });
    });

    on('game:rematch', (p, reply) => {
      const me = online.get(uid);
      const g = games.get(String(p.gameId || ''));
      if (!me || !g || me.gameId !== g.id || !g.over || g.vsCpu) return fail(reply, 'Revanche impossible.');
      if (g.left[0] || g.left[1]) return fail(reply, 'Ton adversaire a quitté la partie.');
      const idx = g.players.findIndex((x) => x.id === uid);
      g.rematch[idx] = true;
      if (g.rematch[0] && g.rematch[1]) {
        destroyGame(g);
        const ng = createGame({ type: g.type, p0: g.players[0].id, p1: g.players[1].id, starter: 1 - g.starter });
        pushGame(ng);
      } else {
        pushGame(g);
      }
      reply({ ok: true });
    });

    on('game:replay', (p, reply) => {
      const me = online.get(uid);
      const g = me && me.gameId && games.get(me.gameId);
      if (!g || !g.vsCpu || !g.over) return fail(reply, 'Impossible de rejouer maintenant.');
      const level = LEVELS.includes(p.level) ? p.level : g.level;
      destroyGame(g);
      const ng = createGame({ type: g.type, p0: uid, p1: null, level, starter: 1 - g.starter });
      pushGame(ng);
      reply({ ok: true });
    });

    on('profile:avatar', (p, reply) => {
      if (!AVATARS.includes(p.avatar)) return fail(reply, 'Avatar invalide.');
      const u = store.getUser(uid);
      u.avatar = p.avatar;
      store.save();
      socket.emit('me:update', { avatar: u.avatar });
      broadcastLobby();
      reply({ ok: true });
    });

    socket.on('disconnect', () => {
      const r = online.get(uid);
      if (!r || r.socketId !== socket.id) return; // remplacé par une connexion plus récente
      if (r.status === 'playing') {
        // En pleine partie : on laisse un délai pour revenir (perte de réseau, changement d'appli…).
        r.disconnected = true;
        const g = r.gameId && games.get(r.gameId);
        if (g && !g.vsCpu) pushGame(g);
        r.graceTimer = setTimeout(() => dropUser(uid), cfg.graceMs);
      } else {
        dropUser(uid);
      }
    });
  });

  /* ================================================================ */
  /* Cycle de vie                                                       */
  /* ================================================================ */

  async function listen(port) {
    try {
      const mode = await store.init();
      console.log(`Stockage des comptes : ${mode === 'postgres' ? 'PostgreSQL (durable)' : 'fichier JSON'}`);
    } catch (e) {
      console.error('⚠️  PostgreSQL injoignable :', e.message);
      console.error('⚠️  Repli sur un fichier : les comptes seront PERDUS au prochain redéploiement. Vérifie DATABASE_URL.');
      store.fallbackToFile();
    }
    if (store.mode === 'fichier' && process.env.RENDER) {
      console.warn('⚠️  Aucune base PostgreSQL configurée (DATABASE_URL) : sur Render gratuit, les comptes sont effacés à chaque redéploiement.');
    }
    return new Promise((resolve, reject) => {
      server.once('error', reject);
      server.listen(port, () => resolve(server.address().port));
    });
  }

  async function close() {
    clearInterval(hitsTimer);
    clearTimeout(lobbyTimer);
    for (const g of games.values()) clearTimers(g);
    for (const inv of invites.values()) clearTimeout(inv.timer);
    for (const r of online.values()) clearTimeout(r.graceTimer);
    try {
      await store.close();
    } catch (e) {
      console.error('Écriture finale impossible :', e.message);
    }
    return new Promise((resolve) => {
      io.close(() => resolve());
    });
  }

  return { app, server, io, store, listen, close };
}

module.exports = { createApp, Store, validateRegistration, C4, RPS, Chess, Dames, Ludo, AVATARS };

if (require.main === module) {
  const instance = createApp();
  const port = Number(process.env.PORT) || 3000;
  instance.listen(port).then((p) => console.log(`Arène des jeux prête sur http://localhost:${p}`));
  for (const sig of ['SIGINT', 'SIGTERM']) {
    process.on(sig, async () => {
      await instance.close();
      process.exit(0);
    });
  }
}

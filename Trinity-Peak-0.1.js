/*
 * Trinity-Peak-0.1.js - A powerful chess engine inspired by tomitankChess 6.0
 * Optimized for stdin/stdout FEN input with UCI move output
 * 
 * Features:
 * - Bitboard representation with magic bitboards
 * - Alpha-beta search with Principal Variation Search (PVS)
 * - Transposition table with Zobrist hashing
 * - Late Move Reduction (LMR)
 * - Killer moves and history heuristic
 * - Quiescence search
 * - Piece-square tables for positional evaluation
 * 
 * Easy to fine-tune via CONFIG object
 */

'use strict';

const readline = require('readline');

// ============================================================================
// CONFIGURATION - Easy to fine-tune
// ============================================================================
const CONFIG = {
    // Search settings
    MAX_DEPTH: 7,                // Maximum search depth
    TIME_LIMIT_MS: 4500,         // Time budget per move (ms)
    MIN_NODES: 1000,             // Minimum nodes before time check
    
    // Algorithm toggles
    USE_PVS: true,               // Principal Variation Search
    USE_LMR: true,               // Late Move Reduction
    USE_QS_CHECKS: false,        // Check extensions in quiescence
    USE_IID: true,               // Internal Iterative Deepening
    
    // LMR parameters
    LMR_BASE: 0.75,
    LMR_FACTOR: 0.25,
    LMR_MIN_DEPTH: 3,
    
    // Aspiration window
    ASPIRATION_DELTA: 25,
    ASPIRATION_MAX: 500,
    
    // Randomness for variety
    RANDOMIZE: false,
    RANDOM_FACTOR: 5,
};

// ============================================================================
// CONSTANTS
// ============================================================================
const EMPTY = 0;
const PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6;
const WHITE = 0, BLACK = 1;
const WHITE_PAWN = 1, WHITE_KNIGHT = 2, WHITE_BISHOP = 3, WHITE_ROOK = 4, WHITE_QUEEN = 5, WHITE_KING = 6;
const BLACK_PAWN = 9, BLACK_KNIGHT = 10, BLACK_BISHOP = 11, BLACK_ROOK = 12, BLACK_QUEEN = 13, BLACK_KING = 14;

const FILES = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'];

// Hash flags
const HASH_EXACT = 0, HASH_LOWER = 1, HASH_UPPER = 2;

// Score constants
const SCORE_NONE = -32768;
const SCORE_MATE = 32000;
const SCORE_DRAW = 0;

// Bitboard helpers using BigInt for 64-bit operations
const C64 = BigInt(0);
const ONE64 = BigInt(1);

// Precomputed attack tables
const pawnAttacksWhite = new Array(64).fill(C64);
const pawnAttacksBlack = new Array(64).fill(C64);
const knightAttacks = new Array(64).fill(C64);
const kingAttacks = new Array(64).fill(C64);
const bishopMask = new Array(64).fill(C64);
const rookMask = new Array(64).fill(C64);

// Magic bitboard tables
let bishopTable = [];
let rookTable = [];
const bishopMagics = new Uint32Array(64);
const rookMagics = new Uint32Array(64);
const bishopShifts = new Uint8Array(64);
const rookShifts = new Uint8Array(64);

// Zobrist keys
const zobristPieces = [];
const zobristCastling = new Uint32Array(16);
const zobristEnPassant = new Uint32Array(64);
let zobristSide = 0n;

// Transposition table (16MB ~ 1M entries x 16 bytes)
const TT_SIZE = 1 << 19;
const TT_MASK = TT_SIZE - 1;
const ttKeys = new BigUint64Array(TT_SIZE);
const ttScores = new Int32Array(TT_SIZE);
const ttBestMoves = new Uint16Array(TT_SIZE);
const ttDepths = new Uint8Array(TT_SIZE);
const ttFlags = new Uint8Array(TT_SIZE);

// History tables
const historyTable = new Int32Array(12 * 64);
const killerMoves = new Int32Array(2 * 128);

// Counter moves
const counterMoves = new Int32Array(12 * 64);

// Capture history
const captureHistory = new Int32Array(12 * 64);

// Root moves storage
let rootMoves = [];

// Search statistics
let nodesSearched = 0;
let startTime = 0;
let stopSearch = false;
let bestMoveFound = 0;

// ============================================================================
// INITIALIZATION
// ============================================================================
function init() {
    initAttackTables();
    initMagicTables();
    initZobrist();
}

function initAttackTables() {
    // Pawn attacks
    for (let sq = 0; sq < 64; sq++) {
        const file = sq % 8;
        const rank = Math.floor(sq / 8);
        
        if (file > 0 && rank < 7) pawnAttacksWhite[sq] |= ONE64 << BigInt(sq + 7);
        if (file < 7 && rank < 7) pawnAttacksWhite[sq] |= ONE64 << BigInt(sq + 9);
        if (file > 0 && rank > 0) pawnAttacksBlack[sq] |= ONE64 << BigInt(sq - 9);
        if (file < 7 && rank > 0) pawnAttacksBlack[sq] |= ONE64 << BigInt(sq - 7);
    }
    
    // Knight attacks
    const knightOffsets = [-17, -15, -10, -6, 6, 10, 15, 17];
    for (let sq = 0; sq < 64; sq++) {
        const file = sq % 8;
        const rank = Math.floor(sq / 8);
        for (const offset of knightOffsets) {
            const target = sq + offset;
            if (target >= 0 && target < 64) {
                const tFile = target % 8;
                const tRank = Math.floor(target / 8);
                if (Math.abs(file - tFile) <= 2 && Math.abs(rank - tRank) <= 2) {
                    knightAttacks[sq] |= ONE64 << BigInt(target);
                }
            }
        }
    }
    
    // King attacks
    for (let sq = 0; sq < 64; sq++) {
        const file = sq % 8;
        const rank = Math.floor(sq / 8);
        for (let df = -1; df <= 1; df++) {
            for (let dr = -1; dr <= 1; dr++) {
                if (df === 0 && dr === 0) continue;
                const tf = file + df;
                const tr = rank + dr;
                if (tf >= 0 && tf < 8 && tr >= 0 && tr < 8) {
                    kingAttacks[sq] |= ONE64 << BigInt(tr * 8 + tf);
                }
            }
        }
    }
    
    // Sliding piece masks
    for (let sq = 0; sq < 64; sq++) {
        const file = sq % 8;
        const rank = Math.floor(sq / 8);
        
        // Bishop mask
        for (let d = 1; d < 8; d++) {
            if (file + d >= 8 || rank + d >= 8) break;
            bishopMask[sq] |= ONE64 << BigInt((rank + d) * 8 + (file + d));
        }
        for (let d = 1; d < 8; d++) {
            if (file - d < 0 || rank + d >= 8) break;
            bishopMask[sq] |= ONE64 << BigInt((rank + d) * 8 + (file - d));
        }
        for (let d = 1; d < 8; d++) {
            if (file + d >= 8 || rank - d < 0) break;
            bishopMask[sq] |= ONE64 << BigInt((rank - d) * 8 + (file + d));
        }
        for (let d = 1; d < 8; d++) {
            if (file - d < 0 || rank - d < 0) break;
            bishopMask[sq] |= ONE64 << BigInt((rank - d) * 8 + (file - d));
        }
        
        // Rook mask
        for (let f = file + 1; f < 8; f++) rookMask[sq] |= ONE64 << BigInt(rank * 8 + f);
        for (let f = file - 1; f >= 0; f--) rookMask[sq] |= ONE64 << BigInt(rank * 8 + f);
        for (let r = rank + 1; r < 8; r++) rookMask[sq] |= ONE64 << BigInt(r * 8 + file);
        for (let r = rank - 1; r >= 0; r--) rookMask[sq] |= ONE64 << BigInt(r * 8 + file);
    }
}

function initMagicTables() {
    // Known good magic numbers
    const bishopMagicNumbers = [
        0x0002020202020202n, 0x0002020202020000n, 0x0002020202000000n, 0x0002020200000000n,
        0x0002020000000000n, 0x0002000400000000n, 0x0002000200000000n, 0x0002000202000000n,
        0x0001010101010101n, 0x0001010101010000n, 0x0001010101000000n, 0x0001010100000000n,
        0x0001010000000000n, 0x0001000200000000n, 0x0001000100000000n, 0x0001000101000000n,
        0x0000808080808080n, 0x0000808080800000n, 0x0000808080000000n, 0x0000808000000000n,
        0x0000800000000000n, 0x0000408000000000n, 0x0000404000000000n, 0x0000404080000000n,
        0x0000404040404040n, 0x0000404040400000n, 0x0000404000000000n, 0x0000400000000000n,
        0x0000200000000000n, 0x0000204000000000n, 0x0000202000000000n, 0x0000202040000000n,
        0x0000202020202020n, 0x0000202020200000n, 0x0000202000000000n, 0x0000200000000000n,
        0x0000100000000000n, 0x0000102000000000n, 0x0000101000000000n, 0x0000101020000000n,
        0x0000101010101010n, 0x0000101010100000n, 0x0000101000000000n, 0x0000100000000000n,
        0x0000080000000000n, 0x0000081000000000n, 0x0000080800000000n, 0x0000080810000000n,
        0x0000080808080808n, 0x0000080808080000n, 0x0000080800000000n, 0x0000080000000000n,
        0x0000040000000000n, 0x0000040800000000n, 0x0000040400000000n, 0x0000040408000000n,
        0x0000040404040404n, 0x0000040404040000n, 0x0000040400000000n, 0x0000040000000000n,
        0x0000020000000000n, 0x0000020400000000n, 0x0000020200000000n, 0x0000020204000000n,
    ];
    
    const rookMagicNumbers = [
        0x0001010101010100n, 0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n,
        0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n, 0x0001010101010100n,
        0x0001010101010100n, 0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n,
        0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n, 0x0001010101010100n,
        0x0001010101010100n, 0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n,
        0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n, 0x0001010101010100n,
        0x0001010101010100n, 0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n,
        0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n, 0x0001010101010100n,
        0x0001010101010100n, 0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n,
        0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n, 0x0001010101010100n,
        0x0001010101010100n, 0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n,
        0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n, 0x0001010101010100n,
        0x0001010101010100n, 0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n,
        0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n, 0x0001010101010100n,
        0x0001010101010100n, 0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n,
        0x0000808080808000n, 0x0000808080808000n, 0x0000808080808000n, 0x0001010101010100n,
    ];
    
    // Initialize bishop tables
    bishopTable = new Array(64);
    for (let sq = 0; sq < 64; sq++) {
        const mask = bishopMask[sq];
        const bits = popcount(mask);
        bishopShifts[sq] = 64 - bits;
        bishopMagics[sq] = Number(bishopMagicNumbers[sq] & 0xFFFFFFFFn);
        
        const indices = 1 << bits;
        bishopTable[sq] = new Uint32Array(indices);
        
        for (let i = 0; i < indices; i++) {
            let occ = C64;
            let temp = BigInt(i);
            let bitIdx = 0;
            while (temp > C64) {
                while (bitIdx < 64 && !(mask & (ONE64 << BigInt(bitIdx)))) bitIdx++;
                if (bitIdx < 64 && (temp & ONE64)) occ |= ONE64 << BigInt(bitIdx);
                temp >>= ONE64;
                bitIdx++;
            }
            bishopTable[sq][i] = Number(computeBishopAttacks(sq, occ) & 0xFFFFFFFFFFFFFFFFn);
        }
    }
    
    // Initialize rook tables
    rookTable = new Array(64);
    for (let sq = 0; sq < 64; sq++) {
        const mask = rookMask[sq];
        const bits = popcount(mask);
        rookShifts[sq] = 64 - bits;
        rookMagics[sq] = Number(rookMagicNumbers[sq] & 0xFFFFFFFFn);
        
        const indices = 1 << bits;
        rookTable[sq] = new Uint32Array(indices);
        
        for (let i = 0; i < indices; i++) {
            let occ = C64;
            let temp = BigInt(i);
            let bitIdx = 0;
            while (temp > C64) {
                while (bitIdx < 64 && !(mask & (ONE64 << BigInt(bitIdx)))) bitIdx++;
                if (bitIdx < 64 && (temp & ONE64)) occ |= ONE64 << BigInt(bitIdx);
                temp >>= ONE64;
                bitIdx++;
            }
            rookTable[sq][i] = Number(computeRookAttacks(sq, occ) & 0xFFFFFFFFFFFFFFFFn);
        }
    }
}

function computeBishopAttacks(sq, occ) {
    let attacks = C64;
    const file = sq % 8;
    const rank = Math.floor(sq / 8);
    
    for (let d = 1; d < 8; d++) {
        if (file + d >= 8 || rank + d >= 8) break;
        const target = (rank + d) * 8 + (file + d);
        attacks |= ONE64 << BigInt(target);
        if (occ & (ONE64 << BigInt(target))) break;
    }
    for (let d = 1; d < 8; d++) {
        if (file - d < 0 || rank + d >= 8) break;
        const target = (rank + d) * 8 + (file - d);
        attacks |= ONE64 << BigInt(target);
        if (occ & (ONE64 << BigInt(target))) break;
    }
    for (let d = 1; d < 8; d++) {
        if (file + d >= 8 || rank - d < 0) break;
        const target = (rank - d) * 8 + (file + d);
        attacks |= ONE64 << BigInt(target);
        if (occ & (ONE64 << BigInt(target))) break;
    }
    for (let d = 1; d < 8; d++) {
        if (file - d < 0 || rank - d < 0) break;
        const target = (rank - d) * 8 + (file - d);
        attacks |= ONE64 << BigInt(target);
        if (occ & (ONE64 << BigInt(target))) break;
    }
    
    return attacks;
}

function computeRookAttacks(sq, occ) {
    let attacks = C64;
    const file = sq % 8;
    const rank = Math.floor(sq / 8);
    
    for (let f = file + 1; f < 8; f++) {
        const target = rank * 8 + f;
        attacks |= ONE64 << BigInt(target);
        if (occ & (ONE64 << BigInt(target))) break;
    }
    for (let f = file - 1; f >= 0; f--) {
        const target = rank * 8 + f;
        attacks |= ONE64 << BigInt(target);
        if (occ & (ONE64 << BigInt(target))) break;
    }
    for (let r = rank + 1; r < 8; r++) {
        const target = r * 8 + file;
        attacks |= ONE64 << BigInt(target);
        if (occ & (ONE64 << BigInt(target))) break;
    }
    for (let r = rank - 1; r >= 0; r--) {
        const target = r * 8 + file;
        attacks |= ONE64 << BigInt(target);
        if (occ & (ONE64 << BigInt(target))) break;
    }
    
    return attacks;
}

function getBishopAttacks(sq, occLow, occHigh) {
    const occ = (BigInt(occHigh) << 32n) | BigInt(occLow >>> 0);
    const masked = (occ & bishopMask[sq]) * BigInt(bishopMagics[sq]);
    const index = Number(masked >> BigInt(bishopShifts[sq]));
    return BigInt(bishopTable[sq][index]);
}

function getRookAttacks(sq, occLow, occHigh) {
    const occ = (BigInt(occHigh) << 32n) | BigInt(occLow >>> 0);
    const masked = (occ & rookMask[sq]) * BigInt(rookMagics[sq]);
    const index = Number(masked >> BigInt(rookShifts[sq]));
    return BigInt(rookTable[sq][index]);
}

function popcount(bb) {
    let count = 0;
    while (bb > C64) {
        bb &= bb - ONE64;
        count++;
    }
    return count;
}

function lsb(bb) {
    if (bb === C64) return -1;
    let count = 0;
    while ((bb & ONE64) === C64) {
        bb >>= ONE64;
        count++;
    }
    return count;
}

function initZobrist() {
    // Initialize piece keys
    for (let p = 0; p < 12; p++) {
        const arr = new Uint32Array(64);
        for (let sq = 0; sq < 64; sq++) {
            arr[sq] = randomZobrist();
        }
        zobristPieces.push(arr);
    }
    
    // Castling keys
    for (let i = 0; i < 16; i++) {
        zobristCastling[i] = randomZobrist();
    }
    
    // En passant keys
    for (let sq = 0; sq < 64; sq++) {
        zobristEnPassant[sq] = randomZobrist();
    }
    
    // Side to move
    zobristSide = BigInt(randomZobrist());
}

let zobristSeed = 0x12345678;
function randomZobrist() {
    zobristSeed ^= zobristSeed << 13;
    zobristSeed ^= zobristSeed >>> 17;
    zobristSeed ^= zobristSeed << 5;
    return zobristSeed >>> 0;
}

// ============================================================================
// POSITION CLASS
// ============================================================================
class Position {
    constructor() {
        this.board = new Uint8Array(64);
        this.sideToMove = WHITE;
        this.castling = 0;
        this.enPassant = -1;
        this.halfMoveClock = 0;
        this.fullMoveNumber = 1;
        this.zobristKey = 0n;
        this.occWhite = 0;
        this.occBlack = 0;
    }
    
    clone() {
        const pos = new Position();
        pos.board = new Uint8Array(this.board);
        pos.sideToMove = this.sideToMove;
        pos.castling = this.castling;
        pos.enPassant = this.enPassant;
        pos.halfMoveClock = this.halfMoveClock;
        pos.fullMoveNumber = this.fullMoveNumber;
        pos.zobristKey = this.zobristKey;
        pos.occWhite = this.occWhite;
        pos.occBlack = this.occBlack;
        return pos;
    }
    
    parseFEN(fen) {
        const parts = fen.trim().split(/\s+/);
        
        // Clear board
        this.board.fill(0);
        this.occWhite = 0;
        this.occBlack = 0;
        this.zobristKey = 0n;
        
        // Piece placement
        let sq = 56; // a8
        for (const char of parts[0]) {
            if (char === '/') {
                sq -= 16; // Go down two ranks (we already incremented)
            } else if (char >= '1' && char <= '8') {
                sq += parseInt(char);
            } else {
                let piece;
                switch (char) {
                    case 'P': piece = WHITE_PAWN; break;
                    case 'N': piece = WHITE_KNIGHT; break;
                    case 'B': piece = WHITE_BISHOP; break;
                    case 'R': piece = WHITE_ROOK; break;
                    case 'Q': piece = WHITE_QUEEN; break;
                    case 'K': piece = WHITE_KING; break;
                    case 'p': piece = BLACK_PAWN; break;
                    case 'n': piece = BLACK_KNIGHT; break;
                    case 'b': piece = BLACK_BISHOP; break;
                    case 'r': piece = BLACK_ROOK; break;
                    case 'q': piece = BLACK_QUEEN; break;
                    case 'k': piece = BLACK_KING; break;
                }
                this.board[sq] = piece;
                this.updateOccupancy(sq, piece);
                this.zobristKey ^= BigInt(zobristPieces[piece - 1][sq]);
                sq++;
            }
        }
        
        // Side to move
        this.sideToMove = (parts[1] === 'w') ? WHITE : BLACK;
        if (this.sideToMove === BLACK) {
            this.zobristKey ^= zobristSide;
        }
        
        // Castling rights
        this.castling = 0;
        if (parts[2] !== '-') {
            if (parts[2].includes('K')) this.castling |= 1;
            if (parts[2].includes('Q')) this.castling |= 2;
            if (parts[2].includes('k')) this.castling |= 4;
            if (parts[2].includes('q')) this.castling |= 8;
        }
        this.zobristKey ^= BigInt(zobristCastling[this.castling]);
        
        // En passant
        this.enPassant = -1;
        if (parts[3] && parts[3] !== '-') {
            const epFile = parts[3].charCodeAt(0) - 97; // 'a' = 0
            const epRank = this.sideToMove === WHITE ? 5 : 2;
            this.enPassant = epRank * 8 + epFile;
            this.zobristKey ^= BigInt(zobristEnPassant[this.enPassant]);
        }
        
        // Half-move clock
        this.halfMoveClock = parts[4] ? parseInt(parts[4]) : 0;
        
        // Full-move number
        this.fullMoveNumber = parts[5] ? parseInt(parts[5]) : 1;
    }
    
    updateOccupancy(sq, piece) {
        const bit = 1 << sq;
        if (piece >= WHITE_PAWN && piece <= WHITE_KING) {
            this.occWhite |= bit;
        } else if (piece >= BLACK_PAWN && piece <= BLACK_KING) {
            this.occBlack |= bit;
        }
    }
    
    removeOccupancy(sq) {
        const bit = ~(1 << sq);
        this.occWhite &= bit;
        this.occBlack &= bit;
    }
    
    getOccBoth() {
        return this.occWhite | this.occBlack;
    }
    
    makeMove(move) {
        const from = (move >> 6) & 63;
        const to = move & 63;
        const piece = (move >> 12) & 15;
        const captured = (move >> 16) & 15;
        const promotion = (move >> 20) & 7;
        const flags = (move >> 24) & 255;
        
        const newPos = this.clone();
        
        // Update zobrist
        newPos.zobristKey ^= BigInt(zobristPieces[piece - 1][from]);
        
        // Remove piece from source
        newPos.board[from] = 0;
        newPos.removeOccupancy(from);
        
        // Handle capture
        if (captured !== 0) {
            newPos.zobristKey ^= BigInt(zobristPieces[captured - 1][to]);
            newPos.removeOccupancy(to);
        }
        
        // Handle en passant capture
        if (flags & 0x02) {
            const epSq = this.enPassant;
            const capSq = epSq + (this.sideToMove === WHITE ? -8 : 8); // Captured pawn is one rank behind the EP square
            const epPawn = this.sideToMove === WHITE ? BLACK_PAWN : WHITE_PAWN;
            newPos.board[capSq] = 0;
            newPos.removeOccupancy(capSq);
            newPos.zobristKey ^= BigInt(zobristPieces[epPawn - 1][capSq]);
        }
        
        // Place piece at destination
        const newPiece = promotion ? (promotion + (this.sideToMove === WHITE ? WHITE_KNIGHT - 1 : BLACK_KNIGHT - 1)) : piece;
        newPos.board[to] = newPiece;
        newPos.updateOccupancy(to, newPiece);
        newPos.zobristKey ^= BigInt(zobristPieces[newPiece - 1][to]);
        
        // Handle castling
        if (flags & 0x04) {
            if (to === 62) { // White kingside
                newPos.board[61] = WHITE_ROOK;
                newPos.occWhite |= (1 << 61);
                newPos.zobristKey ^= BigInt(zobristPieces[WHITE_ROOK - 1][61]);
                newPos.board[63] = 0;
                newPos.occWhite &= ~(1 << 63);
                newPos.zobristKey ^= BigInt(zobristPieces[WHITE_ROOK - 1][63]);
            } else if (to === 58) { // White queenside
                newPos.board[59] = WHITE_ROOK;
                newPos.occWhite |= (1 << 59);
                newPos.zobristKey ^= BigInt(zobristPieces[WHITE_ROOK - 1][59]);
                newPos.board[56] = 0;
                newPos.occWhite &= ~(1 << 56);
                newPos.zobristKey ^= BigInt(zobristPieces[WHITE_ROOK - 1][56]);
            } else if (to === 6) { // Black kingside
                newPos.board[5] = BLACK_ROOK;
                newPos.occBlack |= (1 << 5);
                newPos.zobristKey ^= BigInt(zobristPieces[BLACK_ROOK - 1][5]);
                newPos.board[7] = 0;
                newPos.occBlack &= ~(1 << 7);
                newPos.zobristKey ^= BigInt(zobristPieces[BLACK_ROOK - 1][7]);
            } else if (to === 2) { // Black queenside
                newPos.board[3] = BLACK_ROOK;
                newPos.occBlack |= (1 << 3);
                newPos.zobristKey ^= BigInt(zobristPieces[BLACK_ROOK - 1][3]);
                newPos.board[0] = 0;
                newPos.occBlack &= ~(1 << 0);
                newPos.zobristKey ^= BigInt(zobristPieces[BLACK_ROOK - 1][0]);
            }
        }
        
        // Update castling rights
        const oldCastling = newPos.castling;
        if (piece === WHITE_KING) {
            newPos.castling &= ~3;
        } else if (piece === BLACK_KING) {
            newPos.castling &= ~12;
        } else if (piece === WHITE_ROOK) {
            if (from === 63) newPos.castling &= ~1;
            if (from === 56) newPos.castling &= ~2;
        } else if (piece === BLACK_ROOK) {
            if (from === 7) newPos.castling &= ~4;
            if (from === 0) newPos.castling &= ~8;
        }
        // Rook captures
        if (to === 63) newPos.castling &= ~1;
        if (to === 56) newPos.castling &= ~2;
        if (to === 7) newPos.castling &= ~4;
        if (to === 0) newPos.castling &= ~8;
        
        if (newPos.castling !== oldCastling) {
            newPos.zobristKey ^= BigInt(zobristCastling[oldCastling]);
            newPos.zobristKey ^= BigInt(zobristCastling[newPos.castling]);
        }
        
        // Update en passant
        if (newPos.enPassant !== -1) {
            newPos.zobristKey ^= BigInt(zobristEnPassant[newPos.enPassant]);
        }
        newPos.enPassant = -1;
        if ((flags & 0x01) && Math.abs(to - from) === 16) {
            newPos.enPassant = (from + to) >> 1;
            newPos.zobristKey ^= BigInt(zobristEnPassant[newPos.enPassant]);
        }
        
        // Switch side
        newPos.sideToMove = 1 - newPos.sideToMove;
        newPos.zobristKey ^= zobristSide;
        
        // Update clocks
        if (captured !== 0 || piece === PAWN || piece === 9) {
            newPos.halfMoveClock = 0;
        } else {
            newPos.halfMoveClock = this.halfMoveClock + 1;
        }
        
        if (newPos.sideToMove === WHITE) {
            newPos.fullMoveNumber = this.fullMoveNumber + 1;
        }
        
        return newPos;
    }
    
    isSquareAttacked(sq, byColor) {
        const occWhite = this.occWhite;
        const occBlack = this.occBlack;
        const occBoth = occWhite | occBlack;
        const occLow = occWhite | occBlack;
        const occHigh = 0;
        
        if (byColor === WHITE) {
            // Pawn attacks
            if (pawnAttacksBlack[sq] & BigInt(occWhite)) return true;
            
            // Knight attacks
            if (knightAttacks[sq] & BigInt(occWhite)) {
                for (let i = 0; i < 64; i++) {
                    if ((occWhite & (1 << i)) && this.board[i] === WHITE_KNIGHT) return true;
                }
            }
            
            // King attacks
            if (kingAttacks[sq] & BigInt(occWhite)) {
                for (let i = 0; i < 64; i++) {
                    if ((occWhite & (1 << i)) && this.board[i] === WHITE_KING) return true;
                }
            }
            
            // Sliding pieces
            const bishopOcc = getBishopAttacks(sq, occLow, occHigh);
            if (bishopOcc & BigInt(occWhite)) {
                for (let i = 0; i < 64; i++) {
                    if ((occWhite & (1 << i)) && (bishopOcc & (ONE64 << BigInt(i)))) {
                        const p = this.board[i];
                        if (p === WHITE_BISHOP || p === WHITE_QUEEN) return true;
                    }
                }
            }
            
            const rookOcc = getRookAttacks(sq, occLow, occHigh);
            if (rookOcc & BigInt(occWhite)) {
                for (let i = 0; i < 64; i++) {
                    if ((occWhite & (1 << i)) && (rookOcc & (ONE64 << BigInt(i)))) {
                        const p = this.board[i];
                        if (p === WHITE_ROOK || p === WHITE_QUEEN) return true;
                    }
                }
            }
        } else {
            // Pawn attacks
            if (pawnAttacksWhite[sq] & BigInt(occBlack)) return true;
            
            // Knight attacks
            if (knightAttacks[sq] & BigInt(occBlack)) {
                for (let i = 0; i < 64; i++) {
                    if ((occBlack & (1 << i)) && this.board[i] === BLACK_KNIGHT) return true;
                }
            }
            
            // King attacks
            if (kingAttacks[sq] & BigInt(occBlack)) {
                for (let i = 0; i < 64; i++) {
                    if ((occBlack & (1 << i)) && this.board[i] === BLACK_KING) return true;
                }
            }
            
            // Sliding pieces
            const bishopOcc = getBishopAttacks(sq, occLow, occHigh);
            if (bishopOcc & BigInt(occBlack)) {
                for (let i = 0; i < 64; i++) {
                    if ((occBlack & (1 << i)) && (bishopOcc & (ONE64 << BigInt(i)))) {
                        const p = this.board[i];
                        if (p === BLACK_BISHOP || p === BLACK_QUEEN) return true;
                    }
                }
            }
            
            const rookOcc = getRookAttacks(sq, occLow, occHigh);
            if (rookOcc & BigInt(occBlack)) {
                for (let i = 0; i < 64; i++) {
                    if ((occBlack & (1 << i)) && (rookOcc & (ONE64 << BigInt(i)))) {
                        const p = this.board[i];
                        if (p === BLACK_ROOK || p === BLACK_QUEEN) return true;
                    }
                }
            }
        }
        
        return false;
    }
    
    isInCheck(color) {
        const kingSq = this.findKing(color);
        if (kingSq === -1) return false;
        return this.isSquareAttacked(kingSq, 1 - color);
    }
    
    findKing(color) {
        const kingPiece = color === WHITE ? WHITE_KING : BLACK_KING;
        for (let sq = 0; sq < 64; sq++) {
            if (this.board[sq] === kingPiece) return sq;
        }
        return -1;
    }
    
    isDraw() {
        if (this.halfMoveClock >= 100) return true;
        // TODO: Add repetition detection
        return false;
    }
}

// ============================================================================
// MOVE GENERATION
// ============================================================================
function generateMoves(pos, onlyCaptures) {
    const moves = [];
    const side = pos.sideToMove;
    const them = 1 - side;
    const occBoth = pos.getOccBoth();
    const occLow = occBoth;
    const occHigh = 0;
    
    for (let from = 0; from < 64; from++) {
        const piece = pos.board[from];
        if (piece === 0) continue;
        if ((side === WHITE && piece > WHITE_KING) || (side === BLACK && piece < BLACK_PAWN)) continue;
        
        const pieceType = ((piece - 1) % 8) + 1;
        
        switch (pieceType) {
            case PAWN:
                generatePawnMoves(pos, from, piece, moves, onlyCaptures);
                break;
            case KNIGHT:
                generateKnightMoves(pos, from, piece, moves, onlyCaptures, occBoth);
                break;
            case BISHOP:
                generateSlidingMoves(pos, from, piece, moves, onlyCaptures, occLow, occHigh, getBishopAttacks);
                break;
            case ROOK:
                generateSlidingMoves(pos, from, piece, moves, onlyCaptures, occLow, occHigh, getRookAttacks);
                break;
            case QUEEN:
                generateSlidingMoves(pos, from, piece, moves, onlyCaptures, occLow, occHigh, (sq, ol, oh) => getBishopAttacks(sq, ol, oh) | getRookAttacks(sq, ol, oh));
                break;
            case KING:
                generateKingMoves(pos, from, piece, moves, onlyCaptures, occBoth);
                break;
        }
    }
    
    return moves;
}

function generatePawnMoves(pos, from, piece, moves, onlyCaptures) {
    const side = pos.sideToMove;
    const direction = side === WHITE ? 8 : -8;
    const startRank = side === WHITE ? 6 : 1;
    const promoRank = side === WHITE ? 0 : 7;
    const fromRank = Math.floor(from / 8);
    
    const occBoth = pos.getOccBoth();
    
    // Quiet moves
    if (!onlyCaptures) {
        const to1 = from + direction;
        if (to1 >= 0 && to1 < 64 && pos.board[to1] === 0) {
            const toRank = Math.floor(to1 / 8);
            if (toRank === promoRank) {
                // Promotions
                moves.push(encodeMove(from, to1, piece, 0, 1, 8)); // N
                moves.push(encodeMove(from, to1, piece, 0, 2, 8)); // B
                moves.push(encodeMove(from, to1, piece, 0, 3, 8)); // R
                moves.push(encodeMove(from, to1, piece, 0, 4, 8)); // Q
            } else {
                moves.push(encodeMove(from, to1, piece, 0, 0, 1));
                // Double push
                if (fromRank === startRank) {
                    const to2 = from + 2 * direction;
                    if (pos.board[to2] === 0) {
                        moves.push(encodeMove(from, to2, piece, 0, 0, 1));
                    }
                }
            }
        }
    }
    
    // Captures
    const captureMask = side === WHITE ? pawnAttacksWhite[from] : pawnAttacksBlack[from];
    for (let bb = captureMask; bb > C64; ) {
        const to = lsb(bb);
        bb &= bb - ONE64;
        
        const captured = pos.board[to];
        const isCapture = captured !== 0 && ((side === WHITE && captured >= BLACK_PAWN && captured <= BLACK_KING) || 
                                              (side === BLACK && captured >= WHITE_PAWN && captured <= WHITE_KING));
        const isEP = to === pos.enPassant;
        
        if (isCapture || isEP) {
            const toRank = Math.floor(to / 8);
            if (toRank === promoRank) {
                moves.push(encodeMove(from, to, piece, captured, 1, 10)); // N
                moves.push(encodeMove(from, to, piece, captured, 2, 10)); // B
                moves.push(encodeMove(from, to, piece, captured, 3, 10)); // R
                moves.push(encodeMove(from, to, piece, captured, 4, 10)); // Q
            } else {
                moves.push(encodeMove(from, to, piece, captured, isEP ? 2 : 0, 10));
            }
        }
    }
}

function generateKnightMoves(pos, from, piece, moves, onlyCaptures, occBoth) {
    const side = pos.sideToMove;
    const attacks = knightAttacks[from];
    
    for (let bb = attacks; bb > C64; ) {
        const to = lsb(bb);
        bb &= bb - ONE64;
        
        const captured = pos.board[to];
        const isCapture = captured !== 0 && ((side === WHITE && captured >= BLACK_PAWN && captured <= BLACK_KING) || 
                                              (side === BLACK && captured >= WHITE_PAWN && captured <= WHITE_KING));
        
        if (onlyCaptures && !isCapture) continue;
        if (!isCapture && (occBoth & (1 << to))) continue;
        
        moves.push(encodeMove(from, to, piece, isCapture ? captured : 0, 0, isCapture ? 10 : 0));
    }
}

function generateSlidingMoves(pos, from, piece, moves, onlyCaptures, occLow, occHigh, attackFunc) {
    const side = pos.sideToMove;
    const attacks = attackFunc(from, occLow, occHigh);
    
    for (let bb = attacks; bb > C64; ) {
        const to = lsb(bb);
        bb &= bb - ONE64;
        
        const captured = pos.board[to];
        const isEmpty = captured === 0;
        const isCapture = !isEmpty && ((side === WHITE && captured >= BLACK_PAWN && captured <= BLACK_KING) || 
                                        (side === BLACK && captured >= WHITE_PAWN && captured <= WHITE_KING));
        
        if (onlyCaptures && !isCapture) continue;
        if (!isCapture && !isEmpty) continue;
        
        moves.push(encodeMove(from, to, piece, isCapture ? captured : 0, 0, isCapture ? 10 : 0));
    }
}

function generateKingMoves(pos, from, piece, moves, onlyCaptures, occBoth) {
    const side = pos.sideToMove;
    const attacks = kingAttacks[from];
    
    for (let bb = attacks; bb > C64; ) {
        const to = lsb(bb);
        bb &= bb - ONE64;
        
        const captured = pos.board[to];
        const isEmpty = captured === 0;
        const isCapture = !isEmpty && ((side === WHITE && captured >= BLACK_PAWN && captured <= BLACK_KING) || 
                                        (side === BLACK && captured >= WHITE_PAWN && captured <= WHITE_KING));
        
        if (onlyCaptures && !isCapture) continue;
        if (!isCapture && !isEmpty) continue;
        
        moves.push(encodeMove(from, to, piece, isCapture ? captured : 0, 0, isCapture ? 10 : 0));
    }
    
    // Castling
    if (!onlyCaptures && !pos.isInCheck(side)) {
        if (side === WHITE) {
            if ((pos.castling & 1) && pos.board[61] === 0 && pos.board[62] === 0 && 
                !pos.isSquareAttacked(61, BLACK) && !pos.isSquareAttacked(62, BLACK)) {
                moves.push(encodeMove(from, 62, piece, 0, 4, 0));
            }
            if ((pos.castling & 2) && pos.board[57] === 0 && pos.board[58] === 0 && pos.board[59] === 0 &&
                !pos.isSquareAttacked(59, BLACK) && !pos.isSquareAttacked(58, BLACK)) {
                moves.push(encodeMove(from, 58, piece, 0, 4, 0));
            }
        } else {
            if ((pos.castling & 4) && pos.board[5] === 0 && pos.board[6] === 0 && 
                !pos.isSquareAttacked(5, WHITE) && !pos.isSquareAttacked(6, WHITE)) {
                moves.push(encodeMove(from, 6, piece, 0, 4, 0));
            }
            if ((pos.castling & 8) && pos.board[1] === 0 && pos.board[2] === 0 && pos.board[3] === 0 &&
                !pos.isSquareAttacked(3, WHITE) && !pos.isSquareAttacked(2, WHITE)) {
                moves.push(encodeMove(from, 2, piece, 0, 4, 0));
            }
        }
    }
}

function encodeMove(from, to, piece, captured, flags, promotion) {
    // Bit layout: score[31..24], flags[23..20], promotion[19..17], captured[16..13], piece[12..9], from[8..3], to[2..0]
    return (flags << 20) | ((promotion & 7) << 17) | ((captured & 15) << 13) | ((piece & 15) << 9) | ((from & 63) << 3) | (to & 63);
}

function decodeMove(move) {
    return {
        from: (move >> 3) & 63,
        to: move & 63,
        piece: (move >> 9) & 15,
        captured: (move >> 13) & 15,
        promotion: (move >> 17) & 7,
        flags: (move >> 20) & 15,
        score: move >>> 24
    };
}

// ============================================================================
// EVALUATION
// ============================================================================
const pieceValues = [0, 100, 320, 330, 500, 900, 20000, 0, 100, 320, 330, 500, 900, 20000];

// Piece-square tables (simplified)
const pawnPST = [
     0,  0,  0,  0,  0,  0,  0,  0,
    50, 50, 50, 50, 50, 50, 50, 50,
    10, 10, 20, 30, 30, 20, 10, 10,
     5,  5, 10, 25, 25, 10,  5,  5,
     0,  0,  0, 20, 20,  0,  0,  0,
     5, -5,-10,  0,  0,-10, -5,  5,
     5, 10, 10,-20,-20, 10, 10,  5,
     0,  0,  0,  0,  0,  0,  0,  0
];

const knightPST = [
    -50,-40,-30,-30,-30,-30,-40,-50,
    -40,-20,  0,  0,  0,  0,-20,-40,
    -30,  0, 10, 15, 15, 10,  0,-30,
    -30,  5, 15, 20, 20, 15,  5,-30,
    -30,  0, 15, 20, 20, 15,  0,-30,
    -30,  5, 10, 15, 15, 10,  5,-30,
    -40,-20,  0,  5,  5,  0,-20,-40,
    -50,-40,-30,-30,-30,-30,-40,-50
];

const bishopPST = [
    -20,-10,-10,-10,-10,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5, 10, 10,  5,  0,-10,
    -10,  5,  5, 10, 10,  5,  5,-10,
    -10,  0, 10, 10, 10, 10,  0,-10,
    -10, 10, 10, 10, 10, 10, 10,-10,
    -10,  5,  0,  0,  0,  0,  5,-10,
    -20,-10,-10,-10,-10,-10,-10,-20
];

const rookPST = [
     0,  0,  0,  0,  0,  0,  0,  0,
     5, 10, 10, 10, 10, 10, 10,  5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
     0,  0,  0,  5,  5,  0,  0,  0
];

const queenPST = [
    -20,-10,-10, -5, -5,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5,  5,  5,  5,  0,-10,
     -5,  0,  5,  5,  5,  5,  0, -5,
      0,  0,  5,  5,  5,  5,  0, -5,
    -10,  5,  5,  5,  5,  5,  0,-10,
    -10,  0,  5,  0,  0,  0,  0,-10,
    -20,-10,-10, -5, -5,-10,-10,-20
];

const kingPSTMiddle = [
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -20,-30,-30,-40,-40,-30,-30,-20,
    -10,-20,-20,-20,-20,-20,-20,-10,
     20, 20,  0,  0,  0,  0, 20, 20,
     20, 30, 10,  0,  0, 10, 30, 20
];

function evaluate(pos) {
    let score = 0;
    
    for (let sq = 0; sq < 64; sq++) {
        const piece = pos.board[sq];
        if (piece === 0) continue;
        
        const isWhite = piece <= WHITE_KING;
        const pieceType = ((piece - 1) % 8) + 1;
        const mirrorSq = isWhite ? sq : (sq ^ 56);
        
        let pstValue = 0;
        switch (pieceType) {
            case PAWN: pstValue = pawnPST[mirrorSq]; break;
            case KNIGHT: pstValue = knightPST[mirrorSq]; break;
            case BISHOP: pstValue = bishopPST[mirrorSq]; break;
            case ROOK: pstValue = rookPST[mirrorSq]; break;
            case QUEEN: pstValue = queenPST[mirrorSq]; break;
            case KING: pstValue = kingPSTMiddle[mirrorSq]; break;
        }
        
        const material = pieceValues[piece];
        
        if (isWhite) {
            score += material + pstValue;
        } else {
            score -= material + pstValue;
        }
    }
    
    return pos.sideToMove === WHITE ? score : -score;
}

// ============================================================================
// SEARCH
// ============================================================================
function search(pos, maxDepth) {
    nodesSearched = 0;
    startTime = Date.now();
    stopSearch = false;
    bestMoveFound = 0;
    rootMoves = generateMoves(pos, false);
    
    // Filter legal moves
    rootMoves = rootMoves.filter(move => {
        const newPos = pos.makeMove(move);
        return !newPos.isInCheck(pos.sideToMove);
    });
    
    if (rootMoves.length === 0) return 0;
    
    // Sort root moves
    rootMoves.sort((a, b) => b - a);
    
    let bestScore = -SCORE_MATE;
    let alpha = -SCORE_MATE;
    let beta = SCORE_MATE;
    
    for (let depth = 1; depth <= maxDepth && !stopSearch; depth++) {
        let score;
        
        // Aspiration window
        if (depth >= 4) {
            let delta = CONFIG.ASPIRATION_DELTA;
            alpha = Math.max(-SCORE_MATE, bestScore - delta);
            beta = Math.min(SCORE_MATE, bestScore + delta);
            
            while (true) {
                score = alphabeta(pos, depth, 0, alpha, beta, true);
                if (stopSearch) break;
                
                if (score <= alpha) {
                    alpha = Math.max(-SCORE_MATE, alpha - delta);
                    beta = (alpha + beta) >> 1;
                } else if (score >= beta) {
                    beta = Math.min(SCORE_MATE, beta + delta);
                    delta += delta >> 1;
                } else {
                    break;
                }
                
                if (delta > CONFIG.ASPIRATION_MAX) {
                    alpha = -SCORE_MATE;
                    beta = SCORE_MATE;
                    break;
                }
            }
        } else {
            score = alphabeta(pos, depth, 0, -SCORE_MATE, SCORE_MATE, true);
        }
        
        if (!stopSearch) {
            bestMoveFound = rootMoves[0] || bestMoveFound;
        }
        
        // Time check
        if (nodesSearched >= CONFIG.MIN_NODES && Date.now() - startTime > CONFIG.TIME_LIMIT_MS) {
            stopSearch = true;
        }
    }
    
    return bestMoveFound;
}

function alphabeta(pos, depth, ply, alpha, beta, isPV) {
    if (stopSearch) return 0;
    
    nodesSearched++;
    
    // Check draw
    if (pos.isDraw()) return SCORE_DRAW;
    
    // Check extension
    const inCheck = pos.isInCheck(pos.sideToMove);
    if (inCheck) depth++;
    
    // Quiescence search
    if (depth <= 0) {
        return quiescence(pos, alpha, beta);
    }
    
    // Transposition table lookup
    const key = Number(pos.zobristKey & BigInt(TT_MASK));
    const ttEntry = ttKeys[key] === pos.zobristKey;
    
    if (ttEntry && ttDepths[key] >= depth) {
        const ttScore = ttScores[key];
        const ttFlag = ttFlags[key];
        
        if (ttFlag === HASH_EXACT) return ttScore;
        if (ttFlag === HASH_LOWER && ttScore >= beta) return ttScore;
        if (ttFlag === HASH_UPPER && ttScore <= alpha) return ttScore;
    }
    
    // Internal iterative deepening
    if (CONFIG.USE_IID && isPV && !ttEntry && depth >= 4) {
        alphabeta(pos, depth - 2, ply, alpha, beta, false);
    }
    
    // Generate moves
    const moves = generateMoves(pos, false);
    if (moves.length === 0) {
        return inCheck ? -SCORE_MATE + ply : SCORE_DRAW;
    }
    
    // Score moves
    scoreMoves(pos, moves, ttEntry ? ttBestMoves[key] : 0, ply);
    
    let bestScore = -SCORE_MATE;
    let bestLocalMove = 0;
    let flag = HASH_UPPER;
    let movesSearched = 0;
    
    for (let i = 0; i < moves.length; i++) {
        const move = moves[i];
        const d = decodeMove(move);
        
        // Late move reduction
        let reduction = 0;
        if (CONFIG.USE_LMR && depth >= CONFIG.LMR_MIN_DEPTH && movesSearched >= 4 && !isPV && !inCheck && d.captured === 0) {
            reduction = Math.floor(CONFIG.LMR_BASE + Math.log(movesSearched) * CONFIG.LMR_FACTOR);
        }
        
        const newPos = pos.makeMove(move);
        if (newPos.isInCheck(pos.sideToMove)) continue;
        
        movesSearched++;
        
        let score;
        if (movesSearched === 1) {
            // First move: full PV search
            score = -alphabeta(newPos, depth - 1, ply + 1, -beta, -alpha, isPV);
        } else {
            // Subsequent moves
            if (CONFIG.USE_PVS && isPV && depth >= 2 && reduction < depth - 1) {
                score = -alphabeta(newPos, depth - 2 - reduction, ply + 1, -alpha - 1, -alpha, false);
                if (score > alpha && score < beta) {
                    score = -alphabeta(newPos, depth - 1, ply + 1, -beta, -alpha, true);
                }
            } else {
                score = -alphabeta(newPos, depth - 1 - reduction, ply + 1, -alpha - 1, -alpha, false);
                if (score > alpha && score < beta) {
                    score = -alphabeta(newPos, depth - 1, ply + 1, -beta, -alpha, true);
                }
            }
        }
        
        if (score > bestScore) {
            bestScore = score;
            bestLocalMove = move;
            
            if (score > alpha) {
                alpha = score;
                flag = HASH_EXACT;
                
                if (ply === 0) {
                    bestMoveFound = move;
                    // Move to front for next iteration
                    rootMoves.unshift(rootMoves.splice(i, 1)[0]);
                }
            }
            
            if (score >= beta) {
                flag = HASH_LOWER;
                
                // Store killer move
                if (d.captured === 0) {
                    const ki = ply * 2;
                    if (killerMoves[ki] !== move) {
                        killerMoves[ki + 1] = killerMoves[ki];
                        killerMoves[ki] = move;
                    }
                }
                
                // Update history
                historyTable[d.piece * 64 + d.to] += depth * depth;
                
                break;
            }
        }
    }
    
    // Store in transposition table
    ttKeys[key] = pos.zobristKey;
    ttScores[key] = bestScore;
    ttBestMoves[key] = bestLocalMove;
    ttDepths[key] = depth;
    ttFlags[key] = flag;
    
    return bestScore;
}

function quiescence(pos, alpha, beta) {
    if (stopSearch) return 0;
    
    nodesSearched++;
    
    const standPat = evaluate(pos);
    if (standPat >= beta) return beta;
    if (standPat > alpha) alpha = standPat;
    
    const moves = generateMoves(pos, true);
    
    // Score captures using separate array
    const scores = new Int32Array(moves.length);
    for (let i = 0; i < moves.length; i++) {
        const d = decodeMove(moves[i]);
        scores[i] = (captureHistory[d.piece * 64 + d.to] << 8) | (d.captured * 10 - d.piece);
    }
    
    // Sort moves by score (descending)
    for (let i = 0; i < moves.length - 1; i++) {
        for (let j = i + 1; j < moves.length; j++) {
            if (scores[j] > scores[i]) {
                const tmpScore = scores[i];
                scores[i] = scores[j];
                scores[j] = tmpScore;
                const tmpMove = moves[i];
                moves[i] = moves[j];
                moves[j] = tmpMove;
            }
        }
    }
    
    for (const move of moves) {
        const d = decodeMove(move);
        const newPos = pos.makeMove(move);
        if (newPos.isInCheck(pos.sideToMove)) continue;
        
        const score = -quiescence(newPos, -beta, -alpha);
        
        if (score >= beta) return beta;
        if (score > alpha) alpha = score;
    }
    
    return alpha;
}

function scoreMoves(pos, moves, ttMove, ply) {
    const scores = new Int32Array(moves.length);
    
    for (let i = 0; i < moves.length; i++) {
        const d = decodeMove(moves[i]);
        let score = 0;
        
        // TT move
        if (moves[i] === ttMove) {
            score = 1000000;
        }
        // Captures (MVV-LVA)
        else if (d.captured !== 0) {
            score = 100000 + d.captured * 10 - d.piece + captureHistory[d.piece * 64 + d.to];
        }
        // Killer moves
        else {
            const maxPly = (killerMoves.length / 2) | 0;
            const safePly = Math.max(0, Math.min((ply | 0), maxPly - 1));
            const ki = safePly * 2;
            if (moves[i] === killerMoves[ki]) score = 50000;
            else if (moves[i] === killerMoves[ki + 1]) score = 40000;
            else score = historyTable[d.piece * 64 + d.to];
        }
        
        scores[i] = score;
    }
    
    // Sort moves by score (descending)
    for (let i = 0; i < moves.length - 1; i++) {
        for (let j = i + 1; j < moves.length; j++) {
            if (scores[j] > scores[i]) {
                const tmpScore = scores[i];
                scores[i] = scores[j];
                scores[j] = tmpScore;
                const tmpMove = moves[i];
                moves[i] = moves[j];
                moves[j] = tmpMove;
            }
        }
    }
}

// ============================================================================
// MOVE OUTPUT
// ============================================================================
function moveToString(move) {
    const from = (move >> 6) & 63;
    const to = move & 63;
    const promotion = (move >> 20) & 7;
    
    const fromFile = FILES[from % 8];
    const fromRank = 8 - Math.floor(from / 8);
    const toFile = FILES[to % 8];
    const toRank = 8 - Math.floor(to / 8);
    
    let result = fromFile + fromRank + toFile + toRank;
    
    if (promotion) {
        const promoPieces = ['', 'n', 'b', 'r', 'q'];
        result += promoPieces[promotion];
    }
    
    return result;
}

// ============================================================================
// MAIN
// ============================================================================
init();

const rl = readline.createInterface({ input: process.stdin, terminal: false });

rl.on('line', (fen) => {
    const pos = new Position();
    pos.parseFEN(fen.trim());
    
    // Find best move
    const bestMove = search(pos, CONFIG.MAX_DEPTH);
    
    // Output in UCI format
    if (bestMove !== 0) {
        process.stdout.write(moveToString(bestMove) + '\n');
    } else {
        // Fallback: first legal move
        const moves = generateMoves(pos, false);
        for (const move of moves) {
            const newPos = pos.makeMove(move);
            if (!newPos.isInCheck(pos.sideToMove)) {
                process.stdout.write(moveToString(move) + '\n');
                break;
            }
        }
    }
});

// Chess Agent - Optimized for performance and easy fine-tuning
// Reads FEN from stdin, outputs UCI move to stdout
// Stay alive for reuse between moves

const readline = require('readline');

// ============================================================================
// CONFIGURATION - Easy to fine-tune these parameters
// ============================================================================
const CONFIG = {
    // Search depth (higher = stronger but slower)
    MAX_DEPTH: 4,
    
    // Time limit in milliseconds (leave margin for safety)
    TIME_LIMIT_MS: 4500,
    
    // Piece values (centipawns)
    PIECE_VALUES: {
        'p': 100, 'n': 320, 'b': 330, 'r': 500, 'q': 900, 'k': 20000,
        'P': 100, 'N': 320, 'B': 330, 'R': 500, 'Q': 900, 'K': 20000
    },
    
    // Piece-square tables for positional evaluation (white's perspective)
    PST_PAWN: [
         0,  0,  0,  0,  0,  0,  0,  0,
        50, 50, 50, 50, 50, 50, 50, 50,
        10, 10, 20, 30, 30, 20, 10, 10,
         5,  5, 10, 25, 25, 10,  5,  5,
         0,  0,  0, 20, 20,  0,  0,  0,
         5, -5,-10,  0,  0,-10, -5,  5,
         5, 10, 10,-20,-20, 10, 10,  5,
         0,  0,  0,  0,  0,  0,  0,  0
    ],
    PST_KNIGHT: [
        -50,-40,-30,-30,-30,-30,-40,-50,
        -40,-20,  0,  0,  0,  0,-20,-40,
        -30,  0, 10, 15, 15, 10,  0,-30,
        -30,  5, 15, 20, 20, 15,  5,-30,
        -30,  0, 15, 20, 20, 15,  0,-30,
        -30,  5, 10, 15, 15, 10,  5,-30,
        -40,-20,  0,  5,  5,  0,-20,-40,
        -50,-40,-30,-30,-30,-30,-40,-50
    ],
    PST_BISHOP: [
        -20,-10,-10,-10,-10,-10,-10,-20,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -10,  0,  5, 10, 10,  5,  0,-10,
        -10,  5,  5, 10, 10,  5,  5,-10,
        -10,  0, 10, 10, 10, 10,  0,-10,
        -10, 10, 10, 10, 10, 10, 10,-10,
        -10,  5,  0,  0,  0,  0,  5,-10,
        -20,-10,-10,-10,-10,-10,-10,-20
    ],
    PST_ROOK: [
         0,  0,  0,  0,  0,  0,  0,  0,
         5, 10, 10, 10, 10, 10, 10,  5,
        -5,  0,  0,  0,  0,  0,  0, -5,
        -5,  0,  0,  0,  0,  0,  0, -5,
        -5,  0,  0,  0,  0,  0,  0, -5,
        -5,  0,  0,  0,  0,  0,  0, -5,
        -5,  0,  0,  0,  0,  0,  0, -5,
         0,  0,  0,  5,  5,  0,  0,  0
    ],
    PST_QUEEN: [
        -20,-10,-10, -5, -5,-10,-10,-20,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -10,  0,  5,  5,  5,  5,  0,-10,
         -5,  0,  5,  5,  5,  5,  0, -5,
          0,  0,  5,  5,  5,  5,  0, -5,
        -10,  5,  5,  5,  5,  5,  0,-10,
        -10,  0,  5,  0,  0,  0,  0,-10,
        -20,-10,-10, -5, -5,-10,-10,-20
    ],
    PST_KING_MG: [
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -20,-30,-30,-40,-40,-30,-30,-20,
        -10,-20,-20,-20,-20,-20,-20,-10,
         20, 20,  0,  0,  0,  0, 20, 20,
         20, 30, 10,  0,  0, 10, 30, 20
    ],
    PST_KING_EG: [
        -50,-40,-30,-20,-20,-30,-40,-50,
        -30,-20,-10,  0,  0,-10,-20,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-30,  0,  0,  0,  0,-30,-30,
        -50,-30,-30,-30,-30,-30,-30,-50
    ]
};

// ============================================================================
// BOARD REPRESENTATION
// ============================================================================
class Board {
    constructor() {
        this.squares = new Uint8Array(64); // 0=empty, 1-6=white p,n,b,r,q,k, 7-12=black
        this.whiteToMove = true;
        this.castling = 0; // bits: 0=WK, 1=WQ, 2=BK, 3=BQ
        this.enPassant = -1; // square index or -1
        this.halfmove = 0;
        this.fullmove = 1;
        this.hash = 0;
    }

    static fromFEN(fen) {
        const board = new Board();
        const parts = fen.trim().split(/\s+/);
        
        // Parse piece placement
        let row = 0, col = 0;
        for (const c of parts[0]) {
            if (c === '/') {
                row++;
                col = 0;
            } else if (c >= '1' && c <= '8') {
                col += parseInt(c);
            } else {
                const idx = row * 8 + col;
                const isWhite = c >= 'A' && c <= 'Z';
                const pieceType = 'pnbrqk'.indexOf(c.toLowerCase()) + 1;
                board.squares[idx] = isWhite ? pieceType : pieceType + 6;
                col++;
            }
        }
        
        // Side to move
        board.whiteToMove = parts[1] !== 'b';
        
        // Castling rights
        if (parts[2]) {
            if (parts[2].includes('K')) board.castling |= 1;
            if (parts[2].includes('Q')) board.castling |= 2;
            if (parts[2].includes('k')) board.castling |= 4;
            if (parts[2].includes('q')) board.castling |= 8;
        }
        
        // En passant
        if (parts[3] && parts[3] !== '-') {
            const epCol = parts[3].charCodeAt(0) - 97;
            const epRow = 8 - parseInt(parts[3][1]);
            board.enPassant = epRow * 8 + epCol;
        }
        
        // Halfmove and fullmove counters
        board.halfmove = parseInt(parts[4]) || 0;
        board.fullmove = parseInt(parts[5]) || 1;
        
        board.computeHash();
        return board;
    }

    computeHash() {
        // Simple hash for position
        let h = 0;
        for (let i = 0; i < 64; i++) {
            if (this.squares[i] !== 0) {
                h ^= (this.squares[i] * 31) << (i % 32);
                h = Math.imul(h ^ (h >>> 16), 0x85ebca6b);
                h ^= h >>> 13;
            }
        }
        h ^= this.whiteToMove ? 0x12345678 : 0;
        h ^= this.castling * 0x98765432;
        h ^= this.enPassant * 0xabcdef01;
        this.hash = h >>> 0;
    }

    clone() {
        const b = new Board();
        b.squares = new Uint8Array(this.squares);
        b.whiteToMove = this.whiteToMove;
        b.castling = this.castling;
        b.enPassant = this.enPassant;
        b.halfmove = this.halfmove;
        b.fullmove = this.fullmove;
        b.hash = this.hash;
        return b;
    }

    getPiece(sq) { return this.squares[sq]; }
    isEmpty(sq) { return this.squares[sq] === 0; }
    isWhite(sq) { const p = this.squares[sq]; return p >= 1 && p <= 6; }
    isBlack(sq) { const p = this.squares[sq]; return p >= 7 && p <= 12; }
    isEnemy(sq) { return this.whiteToMove ? this.isBlack(sq) : this.isWhite(sq); }
    isFriend(sq) { return this.whiteToMove ? this.isWhite(sq) : this.isBlack(sq); }

    // Convert square index to algebraic notation
    static sqToStr(sq) {
        const col = sq % 8;
        const row = Math.floor(sq / 8);
        return String.fromCharCode(97 + col) + (8 - row);
    }

    // Convert algebraic to square index
    static strToSq(str) {
        const col = str.charCodeAt(0) - 97;
        const row = 8 - parseInt(str[1]);
        return row * 8 + col;
    }
}

// ============================================================================
// MOVE GENERATION
// ============================================================================
class MoveGenerator {
    static generateMoves(board, onlyCaptures = false) {
        const moves = [];
        const white = board.whiteToMove;
        
        for (let sq = 0; sq < 64; sq++) {
            const piece = board.squares[sq];
            if (piece === 0) continue;
            if (white && piece > 6) continue;
            if (!white && piece <= 6) continue;
            
            const pieceType = ((piece - 1) % 6) + 1; // 1-6
            
            switch (pieceType) {
                case 1: this.generatePawnMoves(board, sq, moves, onlyCaptures); break;
                case 2: this.generateKnightMoves(board, sq, moves, onlyCaptures); break;
                case 3: this.generateBishopMoves(board, sq, moves, onlyCaptures); break;
                case 4: this.generateRookMoves(board, sq, moves, onlyCaptures); break;
                case 5: this.generateQueenMoves(board, sq, moves, onlyCaptures); break;
                case 6: this.generateKingMoves(board, sq, moves, onlyCaptures); break;
            }
        }
        
        return moves;
    }

    static generatePawnMoves(board, sq, moves, onlyCaptures) {
        const white = board.whiteToMove;
        const dir = white ? -8 : 8;
        const startRow = white ? 6 : 1;
        const promoRow = white ? 0 : 7;
        const row = Math.floor(sq / 8);
        const col = sq % 8;
        
        // Single push
        const target = sq + dir;
        if (target >= 0 && target < 64 && board.isEmpty(target)) {
            if (!onlyCaptures) {
                const targetRow = Math.floor(target / 8);
                if (targetRow === promoRow) {
                    for (const promo of ['q', 'r', 'b', 'n']) {
                        moves.push({ from: sq, to: target, promotion: promo });
                    }
                } else {
                    moves.push({ from: sq, to: target });
                    // Double push
                    if (row === startRow) {
                        const target2 = sq + dir * 2;
                        if (board.isEmpty(target2)) {
                            moves.push({ from: sq, to: target2 });
                        }
                    }
                }
            }
        }
        
        // Captures
        for (const dc of [-1, 1]) {
            const targetCol = col + dc;
            if (targetCol < 0 || targetCol > 7) continue;
            const captureSq = sq + dir + dc;
            if (captureSq < 0 || captureSq >= 64) continue;
            
            const canCapture = board.isEnemy(captureSq) || captureSq === board.enPassant;
            if (canCapture) {
                const targetRow = Math.floor(captureSq / 8);
                if (targetRow === promoRow) {
                    for (const promo of ['q', 'r', 'b', 'n']) {
                        moves.push({ from: sq, to: captureSq, promotion: promo, capture: true });
                    }
                } else {
                    moves.push({ from: sq, to: captureSq, capture: true });
                }
            }
        }
    }

    static generateKnightMoves(board, sq, moves, onlyCaptures) {
        const offsets = [-17, -15, -10, -6, 6, 10, 15, 17];
        const row = Math.floor(sq / 8);
        const col = sq % 8;
        
        for (const offset of offsets) {
            const target = sq + offset;
            if (target < 0 || target >= 64) continue;
            
            const targetRow = Math.floor(target / 8);
            const targetCol = target % 8;
            if (Math.abs(row - targetRow) > 2 || Math.abs(col - targetCol) > 2) continue;
            
            if (board.isEmpty(target)) {
                if (!onlyCaptures) moves.push({ from: sq, to: target });
            } else if (board.isEnemy(target)) {
                moves.push({ from: sq, to: target, capture: true });
            }
        }
    }

    static generateSlidingMoves(board, sq, moves, onlyCaptures, directions) {
        const startRank = Math.floor(sq / 8);
        const startFile = sq % 8;

        // directions is expected to be an array of [dFile, dRank] pairs
        for (const [dFile, dRank] of directions) {
            let file = startFile + dFile;
            let rank = startRank + dRank;

            while (file >= 0 && file < 8 && rank >= 0 && rank < 8) {
                const target = rank * 8 + file;

                if (board.isEmpty(target)) {
                    if (!onlyCaptures) {
                        moves.push({ from: sq, to: target });
                    }
                } else if (board.isEnemy(target)) {
                    moves.push({ from: sq, to: target, capture: true });
                    break; // cannot move past an enemy piece
                } else {
                    // own piece is blocking; cannot move further in this direction
                    break;
                }

                file += dFile;
                rank += dRank;
            }
        }
    }

    static generateBishopMoves(board, sq, moves, onlyCaptures) {
        this.generateSlidingMoves(board, sq, moves, onlyCaptures, [[1, 1], [1, -1], [-1, 1], [-1, -1]]);
    }

    static generateRookMoves(board, sq, moves, onlyCaptures) {
        this.generateSlidingMoves(board, sq, moves, onlyCaptures, [[1, 0], [-1, 0], [0, 1], [0, -1]]);
    }

    static generateQueenMoves(board, sq, moves, onlyCaptures) {
        this.generateSlidingMoves(board, sq, moves, onlyCaptures, [[1, 1], [1, -1], [-1, 1], [-1, -1], [1, 0], [-1, 0], [0, 1], [0, -1]]);
    }

    static generateKingMoves(board, sq, moves, onlyCaptures) {
        const offsets = [-9, -8, -7, -1, 1, 7, 8, 9];
        const row = Math.floor(sq / 8);
        const col = sq % 8;
        
        for (const offset of offsets) {
            const target = sq + offset;
            if (target < 0 || target >= 64) continue;
            
            const targetRow = Math.floor(target / 8);
            const targetCol = target % 8;
            if (Math.abs(row - targetRow) > 1 || Math.abs(col - targetCol) > 1) continue;
            
            if (board.isEmpty(target)) {
                if (!onlyCaptures) moves.push({ from: sq, to: target });
            } else if (board.isEnemy(target)) {
                moves.push({ from: sq, to: target, capture: true });
            }
        }
        
        // Castling (only in non-capture mode)
        if (!onlyCaptures && (sq === 60 || sq === 4)) {
            // Simplified castling - just check basic conditions
            if (board.whiteToMove && sq === 60) {
                if ((board.castling & 1) && board.isEmpty(61) && board.isEmpty(62)) {
                    moves.push({ from: 60, to: 62, castle: 'K' });
                }
                if ((board.castling & 2) && board.isEmpty(59) && board.isEmpty(58) && board.isEmpty(57)) {
                    moves.push({ from: 60, to: 58, castle: 'Q' });
                }
            } else if (!board.whiteToMove && sq === 4) {
                if ((board.castling & 4) && board.isEmpty(5) && board.isEmpty(6)) {
                    moves.push({ from: 4, to: 6, castle: 'k' });
                }
                if ((board.castling & 8) && board.isEmpty(3) && board.isEmpty(2) && board.isEmpty(1)) {
                    moves.push({ from: 4, to: 2, castle: 'q' });
                }
            }
        }
    }
}

// ============================================================================
// MOVE EXECUTION
// ============================================================================
class MoveExecutor {
    static makeMove(board, move) {
        const newBoard = board.clone();
        const piece = newBoard.squares[move.from];
        const pieceType = ((piece - 1) % 6) + 1;
        
        // Handle en passant capture
        if (pieceType === 1 && move.to === board.enPassant) {
            const capturedPawnSq = move.to + (board.whiteToMove ? 8 : -8);
            newBoard.squares[capturedPawnSq] = 0;
        }
        
        // Handle castling
        if (move.castle) {
            if (move.castle === 'K') {
                newBoard.squares[61] = newBoard.squares[60];
                newBoard.squares[60] = 0;
                newBoard.squares[62] = piece;
                newBoard.squares[63] = 0;
            } else if (move.castle === 'Q') {
                newBoard.squares[59] = newBoard.squares[60];
                newBoard.squares[60] = 0;
                newBoard.squares[58] = piece;
                newBoard.squares[56] = 0;
            } else if (move.castle === 'k') {
                newBoard.squares[5] = newBoard.squares[4];
                newBoard.squares[4] = 0;
                newBoard.squares[6] = piece;
                newBoard.squares[7] = 0;
            } else if (move.castle === 'q') {
                newBoard.squares[3] = newBoard.squares[4];
                newBoard.squares[4] = 0;
                newBoard.squares[2] = piece;
                newBoard.squares[0] = 0;
            }
        } else {
            // Normal move
            newBoard.squares[move.to] = piece;
            newBoard.squares[move.from] = 0;
            
            // Handle promotion
            if (move.promotion) {
                const promoPiece = 'pnbrqk'.indexOf(move.promotion) + 1;
                newBoard.squares[move.to] = board.whiteToMove ? promoPiece : promoPiece + 6;
            }
        }
        
        // Update castling rights
        if (pieceType === 1) {
            // Pawn move - no castling rights change
        } else if (pieceType === 6) {
            // King move - lose both castling rights
            if (board.whiteToMove) {
                newBoard.castling &= ~3;
            } else {
                newBoard.castling &= ~12;
            }
        } else if (pieceType === 4) {
            // Rook move - lose corresponding castling right
            if (move.from === 63) newBoard.castling &= ~1; // White kingside rook
            else if (move.from === 56) newBoard.castling &= ~2; // White queenside rook
            else if (move.from === 7) newBoard.castling &= ~4; // Black kingside rook
            else if (move.from === 0) newBoard.castling &= ~8; // Black queenside rook
        }
        
        // Also clear castling rights if a rook is captured on its original square
        const capturedPiece = board.squares[move.to];
        if (capturedPiece !== 0) {
            const capturedType = ((capturedPiece - 1) % 6) + 1;
            if (capturedType === 4) {
                if (move.to === 63) newBoard.castling &= ~1; // White kingside rook captured
                else if (move.to === 56) newBoard.castling &= ~2; // White queenside rook captured
                else if (move.to === 7) newBoard.castling &= ~4; // Black kingside rook captured
                else if (move.to === 0) newBoard.castling &= ~8; // Black queenside rook captured
            }
        }
        
        // Update en passant square
        newBoard.enPassant = -1;
        if (pieceType === 1 && Math.abs(move.to - move.from) === 16) {
            newBoard.enPassant = (move.from + move.to) / 2;
        }
        
        // Switch side
        newBoard.whiteToMove = !board.whiteToMove;
        
        // Update halfmove counter
        if (pieceType === 1 || move.capture || move.to === board.enPassant) {
            newBoard.halfmove = 0;
        } else {
            newBoard.halfmove = board.halfmove + 1;
        }
        
        // Update fullmove counter
        if (!board.whiteToMove) {
            newBoard.fullmove = board.fullmove + 1;
        }
        
        newBoard.computeHash();
        return newBoard;
    }
}

// ============================================================================
// EVALUATION FUNCTION
// ============================================================================
class Evaluator {
    static evaluate(board) {
        let score = 0;
        let materialWhite = 0;
        let materialBlack = 0;
        
        for (let sq = 0; sq < 64; sq++) {
            const piece = board.squares[sq];
            if (piece === 0) continue;
            
            const isWhite = piece <= 6;
            const pieceType = ((piece - 1) % 6) + 1;
            const value = CONFIG.PIECE_VALUES[['', 'p', 'n', 'b', 'r', 'q', 'k'][pieceType]];
            
            if (isWhite) {
                materialWhite += value;
                score += value;
                score += this.getPieceSquareValue(pieceType, sq, false);
            } else {
                materialBlack += value;
                score -= value;
                score -= this.getPieceSquareValue(pieceType, sq, true);
            }
        }
        
        // Bonus for mobility (approximate by counting pieces)
        const totalMaterial = materialWhite + materialBlack;
        const isEndgame = totalMaterial < 2600; // Less than queen + rook
        
        // King safety bonus based on game phase
        for (let sq = 0; sq < 64; sq++) {
            const piece = board.squares[sq];
            if (piece === 6) { // White king
                score += this.getPieceSquareValue(6, sq, false, isEndgame);
            } else if (piece === 12) { // Black king
                score -= this.getPieceSquareValue(6, sq, true, isEndgame);
            }
        }
        
        // Side to move bonus
        score += board.whiteToMove ? 30 : -30;
        
        return board.whiteToMove ? score : -score;
    }

    static getPieceSquareValue(pieceType, sq, isBlack, isEndgame = false) {
        let pst;
        switch (pieceType) {
            case 1: pst = CONFIG.PST_PAWN; break;
            case 2: pst = CONFIG.PST_KNIGHT; break;
            case 3: pst = CONFIG.PST_BISHOP; break;
            case 4: pst = CONFIG.PST_ROOK; break;
            case 5: pst = CONFIG.PST_QUEEN; break;
            case 6: pst = isEndgame ? CONFIG.PST_KING_EG : CONFIG.PST_KING_MG; break;
            default: return 0;
        }
        
        const idx = isBlack ? 63 - sq : sq;
        return pst[idx];
    }
}

// ============================================================================
// SEARCH ALGORITHM (Minimax with Alpha-Beta Pruning)
// ============================================================================
class Searcher {
    constructor() {
        this.nodes = 0;
        this.startTime = 0;
        this.bestMove = null;
        this.abort = false;
    }

    search(board, maxDepth) {
        this.nodes = 0;
        this.startTime = Date.now();
        this.bestMove = null;
        this.abort = false;
        
        let bestScore = -Infinity;
        let alpha = -Infinity;
        let beta = Infinity;
        
        const moves = this.orderMoves(board, MoveGenerator.generateMoves(board));
        
        for (const move of moves) {
            if (Date.now() - this.startTime > CONFIG.TIME_LIMIT_MS) {
                this.abort = true;
                break;
            }
            
            const newBoard = MoveExecutor.makeMove(board, move);
            const score = -this.minimax(newBoard, maxDepth - 1, -beta, -alpha);
            
            if (score > bestScore) {
                bestScore = score;
                this.bestMove = move;
            }
            
            alpha = Math.max(alpha, score);
        }
        
        console.error(`Search: depth=${maxDepth}, nodes=${this.nodes}, time=${Date.now() - this.startTime}ms`);
        return this.bestMove;
    }

    minimax(board, depth, alpha, beta) {
        this.nodes++;
        
        if (depth === 0 || this.abort) {
            return Evaluator.evaluate(board);
        }
        
        const moves = this.orderMoves(board, MoveGenerator.generateMoves(board));
        
        if (moves.length === 0) {
            // Check for checkmate or stalemate
            if (this.isInCheck(board)) {
                return -100000 + (100 - depth); // Checkmate
            }
            return 0; // Stalemate
        }
        
        let maxScore = -Infinity;
        
        for (const move of moves) {
            if (this.abort) break;
            
            const newBoard = MoveExecutor.makeMove(board, move);
            const score = -this.minimax(newBoard, depth - 1, -beta, -alpha);
            
            maxScore = Math.max(maxScore, score);
            alpha = Math.max(alpha, score);
            
            if (alpha >= beta) {
                break; // Beta cutoff
            }
        }
        
        return maxScore;
    }

    orderMoves(board, moves) {
        // Simple move ordering: captures first, then promotions
        return moves.sort((a, b) => {
            let scoreA = 0, scoreB = 0;
            if (a.capture) scoreA += 1000;
            if (b.capture) scoreB += 1000;
            if (a.promotion) scoreA += 500;
            if (b.promotion) scoreB += 500;
            if (a.castle) scoreA += 100;
            if (b.castle) scoreB += 100;
            return scoreB - scoreA;
        });
    }

    isInCheck(board) {
        // Find king position
        let kingSq = -1;
        const kingPiece = board.whiteToMove ? 6 : 12;
        for (let sq = 0; sq < 64; sq++) {
            if (board.squares[sq] === kingPiece) {
                kingSq = sq;
                break;
            }
        }
        
        if (kingSq === -1) return true; // Should not happen
        
        // Check if any enemy piece can attack the king
        // Need to generate moves for the opponent, so flip whiteToMove temporarily
        const originalSide = board.whiteToMove;
        board.whiteToMove = !originalSide;
        const enemyMoves = MoveGenerator.generateMoves(board, true);
        board.whiteToMove = originalSide;
        
        for (const move of enemyMoves) {
            if (move.to === kingSq) return true;
        }
        
        return false;
    }
}

// ============================================================================
// MAIN ENTRY POINT
// ============================================================================
function moveToString(move) {
    let str = Board.sqToStr(move.from) + Board.sqToStr(move.to);
    if (move.promotion) {
        str += move.promotion;
    }
    return str;
}

function processFEN(fen) {
    try {
        const board = Board.fromFEN(fen);
        const searcher = new Searcher();
        
        // Iterative deepening
        let bestMove = null;
        for (let depth = 1; depth <= CONFIG.MAX_DEPTH && !searcher.abort; depth++) {
            const move = searcher.search(board, depth);
            if (move && !searcher.abort) {
                bestMove = move;
            }
            if (Date.now() - searcher.startTime > CONFIG.TIME_LIMIT_MS - 500) {
                break;
            }
        }
        
        if (!bestMove) {
            // Fallback: pick first legal move
            const moves = MoveGenerator.generateMoves(board);
            if (moves.length > 0) {
                bestMove = moves[0];
            }
        }
        
        if (bestMove) {
            process.stdout.write(moveToString(bestMove) + '\n');
        } else {
            process.stdout.write('0000\n'); // No legal moves
        }
    } catch (err) {
        console.error('Error:', err.message);
        process.stdout.write('0000\n');
    }
}

// Setup readline interface
const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    terminal: false
});

rl.on('line', (line) => {
    const fen = line.trim();
    if (fen) {
        processFEN(fen);
    }
});

rl.on('close', () => {
    // Clean exit when stdin closes
    process.exit(0);
});

console.error('Chess agent ready. Waiting for FEN input...');

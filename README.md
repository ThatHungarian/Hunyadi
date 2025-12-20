# Hunyadi
A UCI compliant Chess engine  

Unstable at Fast time controls

Features:  

Language & Protocol: C++17, UCI-compliant  
Board Representation: 64-bit bitboards, FEN support, state stacks  
Move Generation: Legal moves, captures-only, castling, en passant, promotion  
Search: Negamax, alpha-beta, iterative deepening, quiescence search, null move pruning, late move reduction, check extension  
Move Ordering: Transposition table, killer moves, history heuristic, MVV-LVA scoring  
Evaluation: Material, piece-square tables, passed/doubled/isolated pawns, bishop pair, rook open files, king safety, mobility, center control  
Time Management: Adaptive allocation with clock/inc support  
Opening Book: Binary Polyglot-style with weighted moves  
Game State: Checkmate, stalemate, insufficient material, 50-move clock, repetition detection  
Hashing: Zobrist-like keys for TT and book  
Optimizations: Built-in intrinsics, atomic stop flag, depth-priority TT replacement, pin detection  

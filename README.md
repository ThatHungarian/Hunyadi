# Hunyadi 4.0

Hunyadi 4.0 is a UCI-compatible chess engine written in C++17.

## Features

- **Bitboard representation** for efficient board and piece handling
- **Magic bitboards** for fast sliding-piece attack generation
- **Principal Variation Search (PVS)** with iterative deepening
- **Lazy SMP** for parallel search
- **Transposition table** with Zobrist hashing
- **Move ordering** using transposition-table moves, killer moves, and history heuristics
- **Quiescence search** for improved tactical stability
- **Position evaluation** with material, piece-square tables, pawn structure, and positional bonuses
- **UCI protocol support** for compatibility with chess GUIs
- **Configurable search options**, including hash size and thread count
- **Perft testing**, self-tests, and benchmarking commands

Hunyadi communicates through the Universal Chess Interface (UCI) protocol.

Example:

```text
uci
isready
position startpos
go depth 10
```

## UCI Options

| Option | Default | Description |
|---|---:|---|
| Hash | 64 MB | Transposition table size |
| Threads | 1 | Number of search threads |
| Clear Hash | — | Clears the transposition table |
| Ponder | false | Enables the pondering option |
| Move Overhead | 20 ms | Time-management overhead |

## Console Commands

| Command | Description |
|---|---|
| `perft <depth>` | Counts legal move-tree nodes at a given depth |
| `selftest` | Runs perft validation on standard positions |
| `bench [depth]` | Benchmarks search performance |
| `d` | Prints the current board, FEN, and position key |
| `eval` | Displays static evaluation |
| `quit` | Exits the engine |

## License

Hunyadi 4.0 is licensed under the Apache License 2.0.

# JAIDE v40 - Zig-based LLM System (KGRU Architecture)

## Overview
JAIDE is a from-scratch LLM system built in Zig 0.14.1 using a custom KGRU (Knowledge-Gated Recurrent Unit) architecture. It includes a custom tokenizer (MGT), neural network training pipeline, inference server, and optional GPU/FPGA acceleration.

## Architecture
- **Language**: Zig 0.14.1 (primary), Python (Modal training scripts)
- **Model**: KGRU architecture with configurable dimensions and layers
- **Tokenizer**: MGT (Magyar/Hungarian Graph Tokenizer) with ~475 vocab tokens
- **Training**: Local via CLI or remote via Modal (GPU cloud)
- **Dataset**: HuggingFaceFW/finephrase (auto-downloaded in Modal scripts)

## Key Files
- `build.zig` / `build.zig.zon` - Build system configuration
- `src/main.zig` - Main entry point, training loop, dataset loading, JSON text extraction
- `src/tokenizer/mgt.zig` - Custom tokenizer with Hungarian vocabulary
- `src/inference_server_main.zig` - HTTP inference server
- `src/scripts/modal_train.py` - Single-node Modal training script
- `src/scripts/modal_distributed_train.py` - Distributed Modal training script
- `src/core_relational/fnds.zig` - Foundational data structures
- `src/index/ssi.zig` - Search/index structures

## Build Commands
- `zig build` - Default build (CPU)
- `zig build -Dgpu=true -Doptimize=ReleaseFast` - GPU build
- `zig build run` - Run interactive JAIDE console

## Dataset Pipeline
- Both Modal scripts auto-download `HuggingFaceFW/finephrase` dataset
- Converts to JSONL format with `{"text": "..."}` per line
- `loadDatasetSamples` in main.zig extracts text from JSON fields: text, content, sentence, article
- Minimum 10 character threshold for text samples
- CLI flag: `--dataset-path /path/to/train.jsonl`

## Workflows
- **Run JAIDE** - Interactive console (`zig build run`)
- **Build** / **Build Release** / **Build GPU** - Compilation
- **Run Tests** / **Run Tensor Tests** / **Run Memory Tests** - Testing
- **Modal Train** / **Modal Distributed Train** - Cloud training
- **Run Inference Server** - HTTP API server

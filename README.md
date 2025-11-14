# An ABC Plugin for Exact Synthesis with Optimal Switching Activity

## 📖 Overview

`pexact` (power-exact) is an exact synthesis command for logic networks optimized for minimal switching activity as a proxy for power consumption. It is based on ABC's `twoexact` command for exact synthesis of 2-input logic networks, but optimizes for switching activity instead of node count.

This plugin implements the algorithms described in the paper **"Exact Synthesis with Optimal Switching Activity"** presented at the Design, Automation and Test in Europe (DATE) conference 2026.

## 🚀 Getting Started (Users)

To use this plugin with ABC:

1. **Clone ABC** from the official repository:

   ```bash
   git clone https://github.com/berkeley-abc/abc.git
   cd abc
   ```

2. **Clone this plugin** into ABC's `src/` directory:

   ```bash
   cd src
   git clone https://github.com/cda-tum/ext-pexact.git
   cd ..
   ```

3. **Build ABC** with the plugin:

   ```bash
   make
   ```

4. **Run ABC** and use the `pexact` command:
   ```bash
   ./abc
   abc 01> pexact
   ```

## 🛠️ Getting Started (Developers)

### Prerequisites

- C++ compiler with C++17 support
- Build tools: `make`, `gcc`/`g++`
- ABC development dependencies

### Development Workflow

This repository uses automated code quality tools:

- **pre-commit hooks**: Ensure code formatting and quality checks before commits

  ```bash
  pip install pre-commit
  pre-commit install
  ```

- **clang-format**: Automatic C++ code formatting
  - Configuration: `.clang-format`
  - Applied automatically via pre-commit hooks

- **GitHub Actions CI**: Automated integration tests on pull requests
  - Tests integration with ABC on Ubuntu, macOS, and Windows
  - Validates the plugin builds and the `pexact` command executes
  - Runs weekly on Fridays to catch upstream ABC changes

### Making Changes

1. Make your modifications to the plugin code
2. Pre-commit hooks will automatically format your code
3. Push your changes and create a pull request
4. CI workflow will validate integration with ABC

## 📚 Citation

If you use this software in your research, please cite:

```bibtex
@inproceedings{walter2026pexact,
  author    = {Walter, Marcel and Feldmeier, Michael and Will, Robert},
  title     = {{Exact Synthesis with Optimal Switching Activity}},
  booktitle = {Design, Automation and Test in Europe (DATE)},
  year      = {2026}
}
```

## 📄 License

This project is licensed under the MIT License - see the [LICENSE.md](LICENSE.md) file for details.

## 🙏 Acknowledgements

This work has been supported by the Bavarian State Ministry for Science and Arts through the
Distinguished Professorship Program.

<p align="center">
<picture>
<source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/munich-quantum-toolkit/.github/refs/heads/main/docs/_static/logo-tum-dark.svg" width="28%">
<img src="https://raw.githubusercontent.com/munich-quantum-toolkit/.github/refs/heads/main/docs/_static/logo-tum-light.svg" width="28%" alt="TUM Logo">
</picture>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; <!-- Non-breaking spaces for spacing -->
<picture>
<img src="https://raw.githubusercontent.com/munich-quantum-toolkit/.github/refs/heads/main/docs/_static/logo-bavaria.svg" width="16%" alt="Coat of Arms of Bavaria">
</picture>
</p>

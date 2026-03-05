#!/usr/bin/env bash
set -e

echo "=== Self-Referring Attention Release Setup ==="
echo ""

# ---------------------------------------------------------------------------
# Lean 4 (via elan)
# ---------------------------------------------------------------------------
echo "[1/2] Lean 4..."

if command -v elan &>/dev/null; then
  echo "  elan found: $(elan --version 2>/dev/null | head -1)"
  echo "  lean: $(lean --version 2>/dev/null | head -1)"
else
  echo "  Installing elan (Lean version manager)..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
  echo "  Done. lean: $(lean --version 2>/dev/null | head -1)"
fi

# ---------------------------------------------------------------------------
# Mathlib (via lake)
# ---------------------------------------------------------------------------
echo "[2/2] Mathlib..."

if [ -d ".lake" ]; then
  echo "  Lake workspace already initialized"
else
  echo "  Initializing Lake workspace (fetches Mathlib)..."
  lake exe cache get
  echo "  Done."
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "=== Setup complete ==="
echo ""
echo "Next steps:"
echo "  lake build              # Build the formalization (~2800 jobs)"
echo "  ./validate.sh           # Run full validation"
echo ""
echo "Verification:"
echo "  cat AttentionLoop/MainTheorem.lean  # Read the Mathlib-only theorem statement"
echo "  lake env lean AttentionLoop/Verification.lean  # Check axiom dependencies"
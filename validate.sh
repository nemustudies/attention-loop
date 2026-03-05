#!/usr/bin/env bash
set -e

# Colors (disabled if stdout is not a terminal, e.g. in CI logs)
if [ -t 1 ]; then
  GREEN='\033[0;32m'
  RED='\033[0;31m'
  YELLOW='\033[0;33m'
  BOLD='\033[1m'
  DIM='\033[2m'
  NC='\033[0m'
else
  GREEN='' RED='' YELLOW='' BOLD='' DIM='' NC=''
fi

echo ""
echo -e "${BOLD}=== Self-Referring Attention Validation ===${NC}"
echo ""

PASS=0
FAIL=0
STEP=0
TOTAL_START=$(date +%s)

step() { STEP=$((STEP + 1)); echo -e "${BOLD}[$STEP]${NC} $1"; }
pass() { echo -e "  ${GREEN}PASS${NC}: $1"; PASS=$((PASS + 1)); }
fail() { echo -e "  ${RED}FAIL${NC}: $1"; FAIL=$((FAIL + 1)); }

# ── Build ─────────────────────────────────────────────────────────
step "Building..."
BUILD_START=$(date +%s)
if ! lake build; then
  BUILD_ELAPSED=$(( $(date +%s) - BUILD_START ))
  fail "Build failed ${DIM}(${BUILD_ELAPSED}s)${NC}"
  echo ""
  echo -e "${RED}${BOLD}=== FAILED: build error ===${NC}"
  exit 1
fi
BUILD_ELAPSED=$(( $(date +%s) - BUILD_START ))
pass "Build succeeded ${DIM}(${BUILD_ELAPSED}s)${NC}"

# ── Sorry check ──────────────────────────────────────────────────
step "Checking for sorry..."
# Match "sorry" as a tactic (not inside comments or doc strings).
count=$(grep -rn --include="*.lean" "^ *sorry" AttentionLoop/ | grep -v ".lake" | wc -l)
if [ "$count" -gt 0 ]; then
  fail "$count lines contain sorry"
  grep -rn --include="*.lean" "^ *sorry" AttentionLoop/ | grep -v ".lake"
else
  pass "No sorry found"
fi

# ── Custom axiom check ──────────────────────────────────────────
step "Checking for custom axioms..."
count=$(grep -rn "^axiom " AttentionLoop/ --include="*.lean" | grep -v ".lake" | wc -l)
if [ "$count" -gt 0 ]; then
  fail "$count custom axioms found"
  grep -rn "^axiom " AttentionLoop/ --include="*.lean" | grep -v ".lake"
else
  pass "No custom axioms"
fi

# ── True placeholder check ──────────────────────────────────────
step "Checking for True placeholders..."
count=$(grep -rn ": True " AttentionLoop/ --include="*.lean" | grep -v ".lake" | grep -v -- "--" | wc -l)
if [ "$count" -gt 0 ]; then
  fail "$count potential True placeholders"
  grep -rn ": True " AttentionLoop/ --include="*.lean" | grep -v ".lake" | grep -v -- "--"
else
  pass "No True placeholders"
fi

# ── #print axioms ───────────────────────────────────────────────
step "Verifying axiom dependencies..."
output=$(lake env lean AttentionLoop/Verification.lean 2>&1)
echo "$output"
if echo "$output" | grep -q "sorryAx"; then
  fail "sorryAx found in axiom dependencies"
elif echo "$output" | grep -q "'mainTheorem' depends on axioms: \[propext, Classical.choice, Quot.sound\]"; then
  pass "mainTheorem uses only standard axioms"
else
  fail "Unexpected axiom output"
fi

# ── MainTheorem import audit ────────────────────────────────────
step "Auditing MainTheorem.lean imports..."
if grep -q "^import AttentionLoop\." AttentionLoop/MainTheorem.lean; then
  fail "MainTheorem.lean imports project files"
  grep "^import AttentionLoop\." AttentionLoop/MainTheorem.lean
else
  pass "MainTheorem.lean imports only Mathlib"
fi

# ── Stats ────────────────────────────────────────────────────────
TOTAL_ELAPSED=$(( $(date +%s) - TOTAL_START ))
echo ""
echo -e "${BOLD}=== Stats ===${NC}"
echo "  Lean files: $(find AttentionLoop/ -name '*.lean' | grep -v .lake | wc -l)"
echo "  Lines of code: $(find AttentionLoop/ -name '*.lean' | grep -v .lake | xargs wc -l | tail -1)"
echo ""
if [ "$FAIL" -gt 0 ]; then
  echo -e "${RED}${BOLD}=== FAILED: $PASS passed, $FAIL failed ($TOTAL_ELAPSED""s) ===${NC}"
  exit 1
else
  echo -e "${GREEN}${BOLD}=== ALL CHECKS PASSED: $PASS passed, 0 failed ($TOTAL_ELAPSED""s) ===${NC}"
fi
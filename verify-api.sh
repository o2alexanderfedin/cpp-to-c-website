#!/bin/bash
# Quick verification script for API endpoints

echo "======================================"
echo "API Endpoints Verification"
echo "======================================"
echo ""

# Check transpiler binary
echo "1. Checking transpiler binary..."
TRANSPILER_PATH="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build/cpptoc"
if [ -x "$TRANSPILER_PATH" ]; then
    echo "   ✓ Transpiler binary found and executable"
else
    echo "   ✗ Transpiler binary NOT found or not executable"
    echo "   Please build the transpiler first:"
    echo "   cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c"
    echo "   mkdir -p build && cd build && cmake .. && make cpptoc"
    exit 1
fi
echo ""

# Check API files
echo "2. Checking API endpoint files..."
files=(
    "src/pages/api/transpile.ts"
    "src/pages/api/validate.ts"
    "src/pages/api/README.md"
)

for file in "${files[@]}"; do
    if [ -f "$file" ]; then
        echo "   ✓ $file"
    else
        echo "   ✗ $file NOT FOUND"
        exit 1
    fi
done
echo ""

# Check frontend adapter
echo "3. Checking frontend adapter compatibility..."
if [ -f "src/adapters/BackendTranspilerAdapter.ts" ]; then
    echo "   ✓ BackendTranspilerAdapter.ts exists"
else
    echo "   ✗ BackendTranspilerAdapter.ts NOT FOUND"
    exit 1
fi
echo ""

# File stats
echo "4. Implementation statistics..."
echo "   Transpile endpoint: $(wc -l < src/pages/api/transpile.ts) lines"
echo "   Validate endpoint: $(wc -l < src/pages/api/validate.ts) lines"
echo "   Documentation: $(wc -l < src/pages/api/README.md) lines"
echo ""

echo "======================================"
echo "✓ All checks passed!"
echo "======================================"
echo ""
echo "Next steps:"
echo "  1. Start dev server: npm run dev"
echo "  2. Test endpoints: ./test-api.sh"
echo "  3. Check TESTING_GUIDE.md for details"
echo ""

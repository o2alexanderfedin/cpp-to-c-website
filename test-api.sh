#!/bin/bash
# Test script for API endpoints

echo "Testing /api/transpile endpoint..."
echo ""

# Test 1: Simple C++ code
echo "Test 1: Simple C++ code"
curl -X POST http://localhost:4321/api/transpile \
  -H "Content-Type: application/json" \
  -d '{
    "source": "#include <iostream>\nint main() {\n    std::cout << \"Hello, World!\" << std::endl;\n    return 0;\n}\n"
  }' | jq '.'

echo ""
echo "---"
echo ""

# Test 2: With ACSL annotations
echo "Test 2: With ACSL annotations"
curl -X POST http://localhost:4321/api/transpile \
  -H "Content-Type: application/json" \
  -d '{
    "source": "int add(int a, int b) { return a + b; }",
    "options": {
      "includeACSL": true,
      "acslLevel": "basic"
    }
  }' | jq '.'

echo ""
echo "---"
echo ""

# Test 3: Invalid syntax
echo "Test 3: Invalid syntax (should fail)"
curl -X POST http://localhost:4321/api/transpile \
  -H "Content-Type: application/json" \
  -d '{
    "source": "int main() { this is invalid syntax }"
  }' | jq '.'

echo ""
echo "---"
echo ""

# Test 4: Validation endpoint - valid code
echo "Test 4: Validation endpoint - valid code"
curl -X POST http://localhost:4321/api/validate \
  -H "Content-Type: application/json" \
  -d '{
    "source": "int main() { return 0; }"
  }' | jq '.'

echo ""
echo "---"
echo ""

# Test 5: Validation endpoint - invalid code
echo "Test 5: Validation endpoint - invalid code"
curl -X POST http://localhost:4321/api/validate \
  -H "Content-Type: application/json" \
  -d '{
    "source": "int main() { invalid syntax here }"
  }' | jq '.'

echo ""
echo "Tests complete!"

// Simple function test
int add(int a, int b) {
    return a + b;
}

int multiply(int x, int y) {
    return x * y;
}

double divide(double numerator, double denominator) {
    if (denominator == 0.0) {
        return 0.0;
    }
    return numerator / denominator;
}

#include <stdio.h>

// The Tritype function as given
int Tritype(double i, double j, double k) {
    int trityp = 0;
    if (i < 0.0 || j < 0.0 || k < 0.0)
        return 3;
    if (i + j <= k || j + k <= i || k + i <= j)
        return 3;
    if (i == j) trityp = trityp + 1;
    if (i == k) trityp = trityp + 1;
    if (j == k) trityp = trityp + 1;
    if (trityp >= 2)
        trityp = 2;
    return trityp;
}

int main() {
    // Test cases: {i, j, k, expected result description}
    struct {
        double i, j, k;
        const char* description;
    } test_cases[] = {
        {3, 3, 3, "Equilateral triangle (expected: 2)"},
        {3, 3, 5, "Isosceles triangle (expected: 1)"},
        {4, 5, 6, "Scalene (other) triangle (expected: 0)"},
        {1, 2, 3, "Not a triangle (violates triangle inequality, expected: 3)"},
        {-1, 2, 3, "Invalid side (negative, expected: 3)"},
        {5, 5, 10, "Not a triangle (equal sides but invalid, expected: 3)"}
    };

    for (int t = 0; t < sizeof(test_cases)/sizeof(test_cases[0]); t++) {
        int result = Tritype(test_cases[t].i, test_cases[t].j, test_cases[t].k);
        printf("Test %d: %s --> Result: %d\n", t + 1, test_cases[t].description, result);
    }

    return 0;
}

int add(int p1, int p2) {
    return p1 + p2;
}
int subtract(int p1, int p2) {
    return p1 - p2;
}
int multiply(int p1, int p2) {
    return p1 * p2;
}
int main() {
    int test_val = 15;
    int result = 0;
    if (test_val < 10) {
        result = add(test_val, 1);
    } else if (test_val < 20) {
        result = subtract(test_val, 1);
    } else {
        result = multiply(test_val, 2);
    }
    return result;
}




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
    int res = multiply(add(1, 2), subtract(5, 3)); // multiply(3, 2) = 6
    return res;
}


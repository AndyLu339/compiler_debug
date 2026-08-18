
int multiply(int p1, int p2) {
    return p1 * p2;
}
int subtract(int p1, int p2) {
    return p1 - p2;
}
int add(int p1, int p2) {
    return p1 + p2;
}
int main() {
    int a = 10;
    int b = 5;
    int c = 0;
    if (multiply(a, b) > 40) {
        c = subtract(a, b);
    } else {
        c = add(a, b);
    }
    return c;
}



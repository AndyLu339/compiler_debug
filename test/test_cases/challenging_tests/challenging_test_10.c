
int add(int p1, int p2) {
    return p1 + p2;
}
int subtract(int p1, int p2) {
    return p1 - p2;
}
int multiply(int p1, int p2) {
    return p1 * p2;
}
int get_five() {
    return 5;
}
int factorial(int n) {
    if (n == 0) return 1;
    return n * factorial(n - 1);
}
int main() {
    int a = 10;
    int b = 5;
    int chain_call_res = add(multiply(subtract(a, b), get_five()), factorial(3));
    return chain_call_res;
}



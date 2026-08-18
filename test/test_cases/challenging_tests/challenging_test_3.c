int factorial(int n) {
    if (n == 0) return 1;
    return n * factorial(n - 1);
}
int main() {
    int res_fact = factorial(10);
    return res_fact;
}



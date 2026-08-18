
int factorial(int n) {
    if (n == 0) return 1;
    return n * factorial(n - 1);
}
int main() {
    int i = 0;
    int sum = 0;
    while (i < 5) {
        sum = sum + factorial(i);
        i = i + 1;
    }
    return sum;
}



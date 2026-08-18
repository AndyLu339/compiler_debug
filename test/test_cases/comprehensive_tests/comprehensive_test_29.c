int is_prime(int num) {
    if (num <= 1) return 0;
    int i = 2;
    while (i * i <= num) {
        if (num % i == 0) return 0;
        i = i + 1;
    }
    return 1;
}
int main() {
    int result = 0;
    if (is_prime(17)) {
        result = 1;
    } else {
        result = 0;
    }
    return result;
}



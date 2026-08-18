
int power(int base, int exp) {
    int result = 1;
    while (exp > 0) {
        result = result * base;
        exp = exp - 1;
    }
    return result;
}
int main() {
    int result = 0;
    result = power(3, 4);
    return result;
}



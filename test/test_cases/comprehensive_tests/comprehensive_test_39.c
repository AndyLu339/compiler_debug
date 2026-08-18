int calculate_complex(int p1, int p2) {
    return (p1 * p2) + (p1 / 2) - (p2 % 3);
}
int main() {
    int a = 10;
    int b = 5;
    int result = 0;
    result = calculate_complex(a, b);
    return result;
}



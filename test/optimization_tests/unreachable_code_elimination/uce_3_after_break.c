int main() {
    int i = 0;
    int sum = 0;
    while (i < 10) {
        sum = sum + i;
        break;
        sum = sum + 100; // Unreachable code
        i = i + 1;
    }
    return sum;
}



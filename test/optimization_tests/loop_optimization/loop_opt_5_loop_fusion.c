int main() {
    int i = 0;
    int sum1 = 0;
    int sum2 = 0;
    while (i < 50) {
        sum1 = sum1 + i;
        i = i + 1;
    }
    i = 0;
    while (i < 50) {
        sum2 = sum2 + (i * 2);
        i = i + 1;
    }
    return sum1 + sum2;
}



int add(int p1, int p2) {
    return p1 + p2;
}
int subtract(int p1, int p2) {
    return p1 - p2;
}
int main() {
    int i = 0;
    int sum = 0;
    while (i < 10) {
        if (i % 2 == 0) {
            sum = sum + add(i, 1);
        } else {
            sum = sum + subtract(i, 1);
        }
        i = i + 1;
    }
    return sum;
}



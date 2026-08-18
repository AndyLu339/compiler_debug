int abs_val(int p) {
    if (p < 0) return -p;
    return p;
}
int main() {
    int i = -5;
    int sum = 0;
    while (i <= 5) {
        sum = sum + abs_val(i);
        i = i + 1;
    }
    return sum;
}



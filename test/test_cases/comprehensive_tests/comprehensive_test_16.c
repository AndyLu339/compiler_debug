
int max(int p1, int p2) {
    if (p1 > p2) return p1;
    return p2;
}
int main() {
    int i = 0;
    int max_val = 0;
    while (i < 10) {
        max_val = max(max_val, i * 2);
        i = i + 1;
    }
    return max_val;
}



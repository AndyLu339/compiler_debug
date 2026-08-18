int main() {
    int i = 0;
    int k = 10;
    int sum = 0;
    while (i < k) {
        sum = sum + i;
        i = i + 1;
        k = k - 1;
    }
    return sum;
}



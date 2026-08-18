int main() {
    int i = 0;
    int j = 0;
    int k = 0;
    int sum = 0;
    while (i < 10) {
        j = 0;
        while (j < 10) {
            k = 0;
            while (k < 10) {
                sum = sum + i + j + k;
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return sum;
}



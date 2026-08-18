
int main() {
    int i = 0;
    int sum = 0;
    while (i < 5) {
        int j = 0;
        while (j < 3) {
            if (i == j) {
                sum = sum + 1;
            } else {
                sum = sum + 2;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return sum;
}



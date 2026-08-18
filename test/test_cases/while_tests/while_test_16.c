
int main() {
    int i = 0;
    int sum = 0;
    while (i < 10) {
        if (i % 3 == 0) {
            sum = sum + 1;
        } else {
            sum = sum + 2;
        }
        i = i + 1;
    }
    return sum;
}



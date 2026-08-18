
int main() {
    int i = 0;
    int sum = 0;
    int x = 10;
    int y = 20;
    while (i < 100) {
        sum = sum + (x * y); // x * y is loop invariant
        i = i + 1;
    }
    return sum;
}




int main() {
    int i = 0;
    int sum = 0;
    while (i < 5) {
        i = i + 1;
        if (i == 2) {
            continue;
            sum = sum + 100; // Unreachable code
        }
        sum = sum + i;
    }
    return sum;
}



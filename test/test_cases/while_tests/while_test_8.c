
int main() {
    int x = 10;
    int y = 20;
    int sum = 0;
    while (x < y && sum < 50) {
        sum = sum + x;
        x = x + 1;
    }
    return sum;
}



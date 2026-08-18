int main() {
    int a = 10;
    int i = 0;
    int sum = 0;
    while (i < a) {
        sum = sum + i;
        if (sum > 20) {
            break;
        }
        i = i + 1;
    }
    return sum;
}



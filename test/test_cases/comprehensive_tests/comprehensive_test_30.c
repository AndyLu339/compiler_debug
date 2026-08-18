
int main() {
    int i = 0;
    int sum = 0;
    while (i < 100) {
        i = i + 1;
        if (i % 7 == 0) {
            continue;
        }
        if (i > 50 && i % 5 == 0) {
            break;
        }
        sum = sum + i;
    }
    return sum;
}



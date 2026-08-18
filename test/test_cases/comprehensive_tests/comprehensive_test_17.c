int main() {
    int score = 85;
    int c = 0;
    if (score > 90) {
        if (score > 95) {
            c = 1;
        } else {
            c = 2;
        }
    } else if (score > 80) {
        c = 3;
    } else {
        c = 4;
    }
    return c;
}



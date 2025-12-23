// Class inheritance
class Shape {
protected:
    int width;
    int height;

public:
    Shape(int w, int h) : width(w), height(h) {}

    virtual int area() {
        return 0;
    }

    int getWidth() const {
        return width;
    }

    int getHeight() const {
        return height;
    }
};

class Rectangle : public Shape {
public:
    Rectangle(int w, int h) : Shape(w, h) {}

    int area() override {
        return width * height;
    }
};

class Triangle : public Shape {
public:
    Triangle(int w, int h) : Shape(w, h) {}

    int area() override {
        return (width * height) / 2;
    }
};

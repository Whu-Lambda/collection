要点：

- 如何定义函数
- 函数返回值
- 匿名函数
- `defer`



# 函数定义

Go 语言定义函数的基本格式如下：

```go
func funcName(name1 type1, name2 type2, ...)(typeA, typeB, ...){
    // body
}
```

示例：

```go
package main

import "fmt"

func add(a int, b int) int {
	return a + b
}

func main() {
	a, b := 1, 2
	fmt.Printf("%d + %d = %d", a, b, add(a, b))
}
```

需要注意的是，函数参数传递的是值，外面的 `a, b `与函数内部的 `a, b` 不同，如果想要改变外部 `a,b` 的值，需要传递指针类型：

```go
package main

import "fmt"

func swap(a, b *int) {
	tmp := *a
	*a = *b
	*b = tmp
}

func main() {

	a, b := 1, 2
	fmt.Printf("a = %d, b = %d\n", a, b)

	swap(&a, &b)
	fmt.Printf("a = %d, b = %d\n", a, b)
}
```

 结果：

```shell
a = 1, b = 2
a = 2, b = 1
```

⚠️ 注意

- `{}` 不能另起一行，以下写法无法编译：

```go
func add(a int, b int) int
{
    return a + b
}
```

Go 语言函数函数参数个数可以不确定，示例如下：

```go
package main

import "fmt"

func findLess(a int, nums ...int) []int {
	fmt.Printf("What's nums: %T: %v\n", nums, nums)
	var less []int
	for _, v := range nums {
		if v < a {
			less = append(less, v)
		}
	}
	return less
}

func main() {
	fmt.Println(findLess(3, 1, 2, 3, 4))
}
```

需要注意的是可变参数要放在固定参数后面，不然会报错，再看一个比较复杂的例子：

```go
package main

import (
	"fmt"
)

func change(s ...string) {
	s[0] = "Go"
}

func main() {
	welcome := []string{"hello", "world"}
	change(welcome...)
	fmt.Println(welcome)
}
```

❓ 请问上述代码的输出结果是什么？为什么？



## 返回值

Go 语言返回值示例如下：

```go
package main

import (
	"fmt"
)

func rectProps(length, width float64) (float64, float64) {
	area := length * width
	perimeter := (length + width) * 2
	return area, perimeter
}
func main() {
	area, perimeter := rectProps(3, 4)
	fmt.Printf("Area: %f, Perimeter: %f\n", area, perimeter)
}
```

还可以写成如下形式：

```go
package main

import (
	"fmt"
)

func rectProps(length, width float64) (area float64, perimeter float64) {
	area = length * width
	perimeter = (length + width) * 2
	return
}
func main() {
	area, perimeter := rectProps(3, 4)
	fmt.Printf("Area: %f, Perimeter: %f\n", area, perimeter)
}
```

💡 要点解读：
- 上述参数与返回参数列表声明还可以称简写成 `func rectProps(length, width float64) (area, perimeter float64)`
- 如果返回的结果用不着，可以用 `_` 忽略：`area, _ := rectProps(3, 4)`

# 匿名函数

Go 语言匿名函数使用示例：

```go
package main

import "fmt"

func main() {
	func() {
		fmt.Println("Hello from anonymous function.")
	}()
}
```

结果：

```shell
Hello from anonymous function.
```

再看一个例子：

```go
package main

import "fmt"

func Click(handle func(event string)) {
	event := "Click event"
	handle(event)

}

func main() {
	handler := func(event string) {
		fmt.Println(event + " is handled.")
	}
	Click(handler)
}
```

输出结果：

```shell
Click event is handled.
```



# `defer` 

`defer` 关键字后的函数调用会在当前函数返回之后执行，有点类似 C++ 的析构函数。如果一个函数体内有多个 `defer`，他们的执行顺序是先进后出，即按压栈的方式执行：

```go
package main

import "fmt"

func sayHi(name string) {
	fmt.Println("Hi", name)

}

func main() {
	defer sayHi("Python")
	defer sayHi("GO")
	defer func() {
		fmt.Println("What's up?")
	}()

	fmt.Println("Hello?")
}
```

结果：

```shell
Hello?
What's up?
Hi GO
Hi Python
```










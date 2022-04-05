本章我们将学习 Go 语言几个常用的数据结构。

要点：

- 数组
- 字典



# 数组

Go 语言可用如下方法声明数组：

```go
package main

import (
	"fmt"
)

func main() {
	// 1. simple array with Zero value
	var a [3]float32
	a[2] = 4
	fmt.Println(a)

	// 2. init
	b := [3]int{1, 2, 3}
	fmt.Println(b)

	// 3. makes the compiler determine the length
	c := [...]int{2, 3, 3, 3}
	fmt.Println(c, "The length: ", len(c))
}
```

💡 要点解读：

- 数组的长度也是类型的一部分。



## 数组赋值是拷贝

把一个数组赋给另一个数组，就有了两个不同的数组：

```go
package main

import "fmt"

func main() {
	a := [...]string{"GO", "C++", "JAVA", "RUST", "Python"}
	b := a
	b[0] = "GO GO GO!"
	fmt.Println("a:", a)
	fmt.Println("b:", b)

	fmt.Println("What if referece?")
	c := &a
	c[0] = "GO Go GO!"
	fmt.Println("a:", a)
	fmt.Println("c:", *c)
}

```

结果：

```shell
a: [GO C++ JAVA RUST Python]
b: [GO GO GO! C++ JAVA RUST Python]
What if referece?
a: [GO Go GO! C++ JAVA RUST Python]
c: [GO Go GO! C++ JAVA RUST Python]
```

## 遍历数组元素

```go
package main

import "fmt"

func main() {
	a := [...]float64{67.7, 89.8, 21, 78}
	for i := 0; i < len(a); i++ {
		fmt.Printf("a[%d] = %.2f  ", i, a[i])
	}

	fmt.Println("")

	for index, value := range a {
		fmt.Printf("a[%d] = %.2f  ", index, value)
	}
}
```

## 高维数组

```go
package main

import "fmt"

func main() {
	a := [3][2]string{
		{"lion", "tiger"},
		{"cat", "dog"},
		{"pigeon", "peacock"},
	}

	fmt.Println(a)
}
```

结果：

```shell
[[lion tiger] [cat dog] [pigeon peacock]]
```

💡 要点提示：

- 左边的维数是外层数组的维数。

## 切片

切片（slice）是数组的部分引用：

```go
package main

import (
	"fmt"
)

func main() {
	// 1. basic
	a := [5]int{76, 77, 78, 79, 80}
	b := a[2:4]
	fmt.Println("b:", b, "lenth:", len(b), "capacity:", cap(b))

	// 2. change
	fmt.Println("What if I change b?")
	b[0] = 66
	fmt.Println("b:", b)
	fmt.Println("a:", a)

	// 3. from scratch
	c := []int{1, 2, 3}
	fmt.Println("c:", c)

	// 4. make
	d := make([]int, 5, 5)
	fmt.Println(d)
}
```

结果：

```shell
b: [78 79] lenth: 2 capacity: 3
What if I change b?
b: [66 79]
a: [76 77 66 79 80]
c: [1 2 3]
[0 0 0 0 0]
```

💡 要点提示：

- 切片的长度是实际元素的个数，容量是元素组长度减去起始坐标。
- 切片截取规则是左闭右开 $[\dots)$，即取 `a[2]` ，不取 `a[4]`
- 注意切片声明与数组声明的一点点区别

## 数组的拼接

```go
package main

import (
	"fmt"
)

func main() {
	var names []string //zero value of a slice is nil
	fmt.Println(names)
	// 1. append to array
	if names == nil {
		names = append(names, "GO", "C++", "Python")
	}
	fmt.Println(names)

	// 2. slice:
	others := []string{"Java", "Rust"}
	names = append(names, others...)
	fmt.Println(names)
}
```

结果：

```shell
[]
[GO C++ Python]
[GO C++ Python Java Rust]
```

# 字典

字典（Map） 是一种常用的数据结构，定义如下：

```go
map[key type]value type
```

示例如下：

```go
package main

import (
	"fmt"
)

func main() {
	// 1. define an empty map
	age := make(map[string]int)
	fmt.Println(age)

	// 2. add some key, value
	age["Go"] = 15
	age["Java"] = 28
	fmt.Println(age)

	// 3. shortcut
	salary := map[string]int{
		"steve": 12000,
		"jamie": 15000,
	}
	fmt.Println(salary)
}
```

结果：

```shell
map[]
map[Go:15 Java:28]
map[jamie:15000 steve:12000]
```

💡 要点提示：

- 不能使用未初始化的字典，如下代码报错：

```go
package main

func main() {
	var items map[string]int
	items["Tom"] = 2000
}
```

## 取值

从字典中取值示例：

```go
package main

import (
	"fmt"
)

func main() {
	age := map[string]int{}
	age["Go"] = 15

	// 1. simple
	fmt.Println(age["Go"])

	// 2. test exists
	value, ok := age["Go"]
	fmt.Println(value, ok)

	value, ok = age["go"]
	fmt.Println(value, ok)
}
```

## 遍历元素

遍历元素示例：

```go
package main

import (
	"fmt"
)

func main() {
	salary := map[string]int{
		"steve": 12000,
		"jamie": 15000,
		"mike":  9000,
	}
	for key, value := range salary {
		fmt.Printf("salary[%s] = %d\n", key, value)
	}
}
```

## 字典赋值是引用

```go
package main

import (
	"fmt"
)

func main() {
	salary := map[string]int{
		"steve": 12000,
		"jamie": 15000,
		"mike":  9000,
	}
	salary2 := salary
	fmt.Println("salary:", salary)
	fmt.Println("salary2:", salary2)

	delete(salary2, "steve")
	fmt.Println("salary:", salary)
	fmt.Println("salary2:", salary2)
}
```


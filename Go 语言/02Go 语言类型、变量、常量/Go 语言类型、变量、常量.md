要点：

- 了解变量声明的几种方法
- 了解简单的几种类型
- 了解常量的声明

# 变量声明

Go 语言声明变量有如下多种方式，请看最常用的一个方法：

```go
package main

import "fmt"

func main() {  
    var age int = 18 // variable declaration
    fmt.Println("My age is", age)
}
```
结果：

```shell
My age is 18
```

💡要点解读：

- 使用关键字 `var` 接变量名 `age` ，再接变量类型 `int`，并初始化为 18。

第二种方法是声明变量，后面再赋值：

```go
package main

import "fmt"

func main() {  
    var age int // variable declaration
    fmt.Println("My age is", age)
    age = 18 // assignment
    fmt.Println("My age is", age)
}
```

结果：

```shell
My age is 0
My age is 18
```

💡要点解读：

- 如果变量声明的时候没有赋值，Go 语言会默认赋零值。

第三种方法可以省略类型声明，可以根据值推断出类型，这种方法的好处是使得代码整洁：

```go
package main

import "fmt"

func main() {  
    var age = 18 // type will be inferred
    fmt.Println("My age is", age)
}
```

结果:

```shell
My age is 18
```

还可以采用 `:=` 进一步简化变量声明和初始化过程：

```go
package main

import "fmt"

func main() {  
    age := 10
    fmt.Println("My age is", age)
}
```

💡要点解读：

- 这种方法只能用于函数内部，不能用于全局变量：

```go
package main

import "fmt"

age := 18 // error: non-declaration statement outside function body
// var age = 18 // ok

func main() {
    fmt.Println("My age is", age)
}
```

- 变量名不能是声明过的：

```go
package main

import "fmt"

func main() {
	var age = 18
	fmt.Println("My age is", age)
	age := 42 // no new variables on left side of :=
	fmt.Println("My age is", age)
}
```

## 多个变量一起声明的方法

多个变量一起声明示例：

```go
package main

import "fmt"

func main() {
	var width, height int = 100, 50
	fmt.Println("width is: ", width, "height is: ", height)

	var name, age = "lambda", 2
	fmt.Println("name is: ", name, "age is: ", age)

	var (
		price = 9.90
		count int
	)
	fmt.Println("price is: ", price, "count is: ", count)
}
```

输出：

```shell
width is:  100 height is:  50
name is:  lambda age is:  2
price is:  9.9 count is:  0
```

## 使用 `:=` 声明多个变量的重复声明

Go 的错误处理机制使得经常有函数返回 `error` 的情况。若您使用 `:=` 将函数的返回值声明为变量：

```go
foo, err := f() // Declares foo and err
bar, err2 := g() // Declares bar and err2
// ... err3, err4, ...
```

过多的变量也许会带来不便。您可能希望复用第一次声明的 `err`：

```go
foo, err := f()

var bar T // Declares only bar
bar, err = g() // assignments, not declaration
```

或许这过于繁复，您希望有更简单的办法。幸运的是，当您使用 `:=` 声明超过一个变量的时候，Go 会自动声明**未声明过**的变量，其他变量则为赋值。

```go
foo, err := f() // Declares foo and err
bar, err := g() // Valid, err has been overwritten.
```

您可以尝试运行以下的 demo：

```go
package main

import (
	"fmt"
)

func f() (int, error) {
	return 1, fmt.Errorf("error in f()")
}

func g() (float64, error) {
	return 2.0, fmt.Errorf("error in g()")
}

func main() {
	foo, err := f()
	fmt.Printf("Address of err: %p\n", &err)
	bar, err := g()
	fmt.Printf("Address of err: %p\n", &err)
	fmt.Printf("foo: %d, bar: %f\n", foo, bar)
}
```

可能的输出：

```
Address of err: 0xc00003a250
Address of err: 0xc00003a250
foo: 1, bar: 2.000000
```


# 类型

Go 语言内置如下简单类型：

- bool
- Numeric Types
  - int8, int16, int32, int64, int
  - uint8, uint16, uint32, uint64, uint
  - float32, float64
  - complex64, complex128
  - byte
  - rune
- string

💡要点解读：

- int 与 uint 的长度在 32 位机器上是 32 位，64 位机器是 64 位。
- byte 是 uint8 的别称，rune 是 int32 的别称。

示例：

```go
package main

import "fmt"

func main() {
	a := true
	b := false
	fmt.Printf("a: %v Typeof a: %T, b: %v Typeof b: %T\n", a, a, b, b)
	c := a && b
	fmt.Println("c:", c)
	d := a || b
	fmt.Println("d:", d)

	c1 := complex(5, 7)
	c2 := 8 + 27i
	cadd := c1 + c2
	fmt.Println("sum:", cadd)
	cmul := c1 * c2
	fmt.Println("product:", cmul)

	first := "Hello"
	last := "World"
	name := first + " " + last
	fmt.Println("My name is", name)
}

```

结果：

```shell
a: true Typeof a: bool, b: false Typeof b: bool
c: false
d: true
sum: (13+34i)
product: (-149+191i)
My name is Hello World
```

简单变量类型转换：

```go
package main

import (
	"fmt"
)

func main() {
	i := 1               // int
	j := 1.5             // float64
	sumint := i + int(j) // j is converted to int
	fmt.Println(sumint)

	sumfloat := float64(i) + j // i is converted to float64
	fmt.Println(sumfloat)
}
```

结果：

```shell
2
2.5
```



# 常量声明

Go 使用 `const` 声明常量，声明时必须初始化，且常量不能改变其值：

```go
package main

import "fmt"

func main() {
	const pi = 3.1415926
	fmt.Println(pi)
	// pi = 3.14
}
```

## 特殊记号 `iota`

在声明多个常量时，可以用 `iota` 简化：

```go
package main

import "fmt"

func main() {
	const (
		a = iota
		b
		c
	)
	fmt.Println(a, b, c)
}
```

结果：

```shell
0 1 2
```

再看一个例子：

```go
package main

import "fmt"

func main() {
	const (
		a, a1 = iota, iota + 1
		b, b2 = iota, iota * 2
		c     = iota * 3
	)
	fmt.Println(a, a1, b, b2, c)
}
```

结果：

```shell
0 1 1 2 6
```

💡要点解读：

- `iota` 在 `const ()` 声明中，第一行表示 0，第二行表示 1 依次类推。
- `iota` 只能在 `const ()` 使用。


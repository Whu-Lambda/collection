要点：

- 基本用法
- 底层表示
- 空接口
- 类型断言

# 基本用法

Go 语言的 Interface 与其他语言的 Interface 所表达的含义一致：是一系列方法声明。当有一个结构体实现了该 Interface 中所有方法的时候，他就实现了该 Interface。

我们来看一个例子：

```go
package main

import (
	"fmt"
)

type Product interface {
	Total() float32
}

type Orange struct {
	Base     float32
	Discount float32
	Amount   float32
}

func (o Orange) Total() float32 {
	return o.Base * o.Discount * o.Amount
}

func main() {
	orange := Orange{Base: 6.98, Discount: 1.0, Amount: 5}
	var p Product
	p = orange

	fmt.Println(p.Total())
}
```

📝 要点解读

-  `Product` 是一个 Interface，它有一个计算总价的方法：`Total` ，然后我们为 `Orange` 结构体实现了这个方法。主函数声明了两个变量，一个是结构体类型的 `orange`，另一个是接口类型的 `p`，然后 `p=orange`，最后 `p` 调用 `Product` 方法计算出总价。

阅读上述例子，你可能觉得定义接口好像有点多余，假设我不定义那个接口类型，我也能正常调用结构体方法计算总价啊。

现在我们有一个购物车，需要计算所有商品的价格：

```go
package main

import (
	"fmt"
)

type Product interface {
	Total() float32
}

type Orange struct {
	Base     float32
	Discount float32
	Amount   float32
}

func (o Orange) Total() float32 {
	return o.Base * o.Discount * o.Amount
}

func Cart(products []Product) (total float32) {
	for _, product := range products {
		total += product.Total()
	}
	return
}

func main() {
	orange := Orange{Base: 6.98, Discount: 1.0, Amount: 5}

	var products = []Product{orange}

	fmt.Println(Cart(products))
}
```

结果：

```shell
34.9
```

现在我们可以加入其他商品：

```go
package main

import (
	"fmt"
)

type Product interface {
	Total() float32
}

type Orange struct {
	Base     float32
	Discount float32
	Amount   float32
}

func (o Orange) Total() float32 {
	return o.Base * o.Discount * o.Amount
}

type TV struct {
	Base     float32
	Discount float32
	Amount   float32
}

func (tv TV) Total() float32 {
	return tv.Base*tv.Discount*tv.Amount - 500.0 // 满4000减500
}

func Cart(products []Product) (total float32) {
	for _, product := range products {
		total += product.Total()
	}
	return
}

func main() {
	orange := Orange{Base: 6.98, Discount: 1.0, Amount: 5}
	tv := TV{Base: 5000, Discount: 1.0, Amount: 1.0}
	var products = []Product{orange, tv}

	fmt.Println(Cart(products))
}
```

结果：

```shell
4534.9
```

📝 要点解读

- 以上例子表明 Interface 有一个显著的优点：求同存异，只要实现了相关的接口，我们就可以把它们放到一起。

# Interface 底层表示

Interface 在底层可以看成一个元组：`(type, value)`，`type, value` 来自具体结构：

```go
func Cart(products []Product) (total float32) {
	for _, product := range products {
		total += product.Total()
		fmt.Printf("What's product: %T: %v\n", product, product)
	}
	return
}
```

打印结果：

```go
What's product: main.Orange: {6.98 1 5}
What's product: main.TV: {5000 1 1}
```

# 空接口

空接口没有一个方法，由于空接口没有一个方法，可以视为所有的类型都实现了这个接口。

```go
package main

import (
	"fmt"
)

func describe(i interface{}) {
	fmt.Printf("Type = %T, value = %v\n", i, i)
}

func main() {
	s := "Hello World"
	describe(s)
	i := 55
	describe(i)
	user := struct {
		name string
	}{
		name: "Gopher",
	}
	describe(user)
}
```

结果：

```shell
Type = string, value = Hello World
Type = int, value = 55
Type = struct { name string }, value = {Gopher}
```

空接口可以当做 `Any` 类型。

# 类型断言

可以用如下语法断言一个 Interface 的具体类型：

```go
package main

import (
	"fmt"
)

func assert(i interface{}) {
	s := i.(int)
	fmt.Println(s)
}
func main() {
	var s interface{} = 56
	assert(s)
	var i = 56.0
	assert(i)
}
```

结果：

```shell
56
panic: interface conversion: interface {} is float64, not int
```

如果不想报错，可以使用如下的方法：

```go
package main

import (
	"fmt"
)

func assert(i interface{}) {
	s, ok := i.(int)
	if ok {
		fmt.Println(s, "is int")
	} else {
		fmt.Println(i, "is not int")
	}
}
func main() {
	var s interface{} = 56
	assert(s)
	var i = 56.0
	assert(i)
}
```

结果：

```shell
56 is int
56 is not int
```

还可以做类型判断：

```go
package main

import (
	"fmt"
)

func findType(i interface{}) {
	switch i.(type) {
	case string:
		fmt.Println(i.(string), ": I am a string")
	case int:
		fmt.Println(i.(int), ": I am a int")
	default:
		fmt.Printf("Unknown type\n")
	}
}
func main() {
	findType("Naveen")
	findType(77)
	findType(89.98)
}
```

结果：

```shell
Naveen : I am a string
77 : I am a int
Unknown type
```

要点：

- 条件控制
- 循环控制

# 条件控制

Go 语言的条件控制语句格式如下：

```go
if cond1 {  
	// stat1
} else if cond2 {
    // stat2
} else {
    // stat3
}
```

看一个例子：

```go
package main

import (
	"fmt"
)

func main() {
	score := 99
	if score < 60 {
		fmt.Println("You need more practice.")
	} else if score < 80 {
		fmt.Println("Good!")
	} else {
		fmt.Println("Excellent!")
	}
}
```

运行结果：

```shell
Excellent!
```

Go 语言还提供了如下语法，可以使得条件语句更加简洁：

```go
if assignment-statement; condition {  
}
```

以上示例可以写成：

```go
package main

import (
	"fmt"
)

func main() {
	if score := 99; score < 60 {
		fmt.Println("You need more practice.")
	} else if score < 80 {
		fmt.Println("Good!")
	} else {
		fmt.Println("Excellent!")
	}
}
```

这种模式会经常在错误处理时用到：

```go
package main

import (
	"errors"
	"fmt"
)

func divide(a, b float64) (float64, error) {
	if b == 0.0 {
		return 0.0, errors.New("divide by zero")
	}
	return a / b, nil
}

func main() {
	if result, error := divide(2, 0.0); error != nil {
		fmt.Println(error)
	} else {
		fmt.Println(result)
	}
}
```

打印结果：

```shell
divide by zero
```

⚠️ 容易出错的点

- `{}` 不能另起一行：

```go
if a == 0
{
    // do something
}
```

- `else ` 也不能另起一行：

```go
if a < 0{
    // do something
}
else {
    // do other thing
}
```



# `Switch` 语句

Go 语言的 `Switch`  语句有如下几种形式：

```go
package main

import "fmt"

func main() {

	switch day := 4; day {
	case 1:
		fmt.Println("Monday")
	case 2:
		fmt.Println("Tuesday")
	case 3:
		fmt.Println("Wednesday")
	case 4:
		fmt.Println("Thursday")
	case 5:
		fmt.Println("Friday")
	case 6:
		fmt.Println("Saturday")
	case 7:
		fmt.Println("Sunday")
	default:
		fmt.Println("Invalid")
	}
}
```

表达式：

```go
package main

import "fmt"

func main() {
	var value int = 2

	switch {
	case value == 1:
		fmt.Println("Hello")
	case value == 2:
		fmt.Println("Bonjour")
	case value == 3:
		fmt.Println("Namstay")
	default:
		fmt.Println("Invalid")
	}
}
```

多种可能：

```go
package main

import (
	"fmt"
)

func main() {
	letter := "i"
	fmt.Printf("Letter %s is a ", letter)
	switch letter {
	case "a", "e", "i", "o", "u":
		fmt.Println("vowel")
	default:
		fmt.Println("not a vowel")
	}
}
```

`fallthrough`

```go
package main

import (
	"fmt"
)

func main() {
	switch num := 42; {
	case num < 50:
		fmt.Printf("%d is lesser than 50\n", num)
		fallthrough
	case num < 100:
		fmt.Printf("%d is lesser than 100\n", num)
		fallthrough
	case num < 200:
		fmt.Printf("%d is lesser than 200\n", num)
	}
}
```

结果：

```shell
42 is lesser than 50
42 is lesser than 100
42 is lesser than 200
```

⚠️ 注意

- 不能有两个一样的 `case` 语句。




# 循环语句

Go 语言循环语句有如下定义方式：

```go
for initialization; condition; post{
	// statements....
}
```

例如：

```go
package main

import "fmt"

func main() {
	for i := 0; i < 4; i++ {
		fmt.Println(i)
	}
}
```

把 `post` 放到循环体内也行：

```go
package main

import "fmt"

func main() {
	for i := 0; i < 4; {
		fmt.Println(i)
		i++
	}
}
```

或者像 C 语言 `while` 那样：

```go
package main

import "fmt"

func main() {
	i := 0
	for i < 4 {
		fmt.Println(i)
		i++
	}
}
```

无限循环：

```go
package main

import "fmt"

func main() {
	i := 0
	for {
		fmt.Println(i)
		i++
	}
}
```

还可以使用 `range` ：

```go
for i, j:= range rvariable{
   // statement..
}
```

例子：

```go
package main

import "fmt"

func main() {
	// array
	arr := []string{"hello", "go", "lang"}
	for index, value := range arr {
		fmt.Println(index, value)
	}

	// String
	for i, j := range "abc" {
		fmt.Printf("The index number of %c is %d\n", j, i)
	}

	//  map
	mmap := map[int]string{
		22: "Hello",
		33: "Go",
	}
	for key, value := range mmap {
		fmt.Println(key, value)
	}

	// channal
	chnl := make(chan int)
	go func() {
		chnl <- 100
		chnl <- 1000
		chnl <- 10000
		chnl <- 100000
		close(chnl)
	}()
	for i := range chnl {
		fmt.Println(i)
	}
}

```

结果：

```shell
0 hello
1 go
2 lang
The index number of a is 0
The index number of b is 1
The index number of c is 2
22 Hello
33 Go
100
1000
10000
100000
```








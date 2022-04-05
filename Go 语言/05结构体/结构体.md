要点：

- 结构体声明
- 结构体方法



# 结构体

Go 语言结构体使用示例：

```go
package main

import (
	"fmt"
)

type Employee struct {
	firstName string
	lastName  string
	age       int
	salary    int
}

func main() {

	emp1 := Employee{
		firstName: "Thomas",
		age:       23,
		salary:    15000,
		lastName:  "Anderson",
	}

	emp2 := Employee{"Sam", "Paul", 29, 18000}

	fmt.Println(emp1)
	fmt.Println(emp2)
}
```

打印结果：

```shell
{Thomas Anderson 23 15000}
{Sam Paul 29 18000}
```

结构体属性 `get` 与 `set` 示例：

```go
package main

import (
	"fmt"
)

type Employee struct {
	firstName string
	lastName  string
	age       int
	salary    int
}

func main() {

	emp1 := Employee{
		firstName: "Thomas",
		age:       23,
		salary:    15000,
		lastName:  "Anderson",
	}

	fmt.Println(emp1.age)
	emp1.age = 25
	fmt.Println(emp1.age)
}
```

结构体指针：

```go
package main

import (
	"fmt"
)

type Employee struct {
	firstName string
	lastName  string
	age       int
	salary    int
}

func main() {
	emp1 := &Employee{
		firstName: "Sam",
		lastName:  "Anderson",
		age:       55,
		salary:    6000,
	}
	fmt.Println((*emp1).age)
	fmt.Println(emp1.age)
}
```

💡 提示：

- 我们发现两种指针用法一样

结构体零值（zero values）:

```go
package main

import (
	"fmt"
)

type Employee struct {
	firstName string
	lastName  string
	age       int
	salary    int
}

func main() {

	var emp1 Employee
	emp2 := Employee{
		firstName: "Thomas",
		lastName:  "Anderson",
	}

	fmt.Println(emp1)
	fmt.Println(emp2)
}
```

输出结果：

```shell
{  0 0}
{Thomas Anderson 0 0}
```

结构体嵌套：

```go
package main

import (
	"fmt"
)

type Name struct {
	firstName string
	lastName  string
}

type Employee struct {
	name   Name
	age    int
	salary int
}

func main() {

	emp1 := Employee{
		name: Name{
			firstName: "Thomas",
			lastName:  "Anderson",
		},
		age:    21,
		salary: 20000,
	}

	fmt.Println(emp1)
	fmt.Println(emp1.name)

}
```

打印结果：

```shell
{{Thomas Anderson} 21 20000}
{Thomas Anderson}
```

结构体组合：

```go
package main

import (
	"fmt"
)

type Name struct {
	firstName string
	lastName  string
}

type Employee struct {
	age    int
	salary int
	Name
}

func main() {

	name := Name{
		firstName: "go",
		lastName:  "lang",
	}
	var emp1 = Employee{
		42,
		20000,
		name,
	}
	fmt.Println(emp1)
	fmt.Println(emp1.firstName)

}
```

结果：

```shell
{42 20000 {go lang}}
go
```

# 结构体方法

结构体方法定义如下：

```go
func(thisName Type) MethodName(parameter List)(return Types){
	// body
}
```

💡 提示：

- 其中 `thisName` 相当于其他语言的 `this` 或 `self`，名字可以任取，`Type` 就是结构体。

```go
package main

import (
	"fmt"
)

type Employee struct {
	name string
	age  int
}

func (e Employee) show() {
	fmt.Println(e)
}

func (this Employee) changeName(newName string) {
	this.name = newName
}

func (this *Employee) changeAge(newAge int) {
	this.age = newAge
}

func main() {
	e := Employee{
		name: "Go Lang",
		age:  15,
	}
	e.show()
	// what's up?
	e.changeName("Python")
	e.show()
    
	// How about pointer？
	(&e).changeAge(51)
	e.show()
}
```




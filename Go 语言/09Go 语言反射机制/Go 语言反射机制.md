要点：

- 反射基本用法
- 获取结构体字段信息
- 获取结构体 `Tag`



# 反射基本用法

Go 语言的变量可以看做一个类型与值的序偶 `(type, value)`，利用反射机制，可以在程序运行时获取相关信息：

```go
package main

import (
	"fmt"
	"reflect"
)

func ReflectVar(arg interface{}) {
	t := reflect.TypeOf(arg)
	v := reflect.ValueOf(arg)
	fmt.Printf("Type: %v, Value: %v\n", t, v)
}

func main() {
	x := 3.14
	ReflectVar(x)
}
```

结果：

```shell
Type: float64, Value: 3.14
```

# 获取结构体字段信息

```go
package main

import (
	"fmt"
	"reflect"
)

type User struct {
	ID   uint
	Name string
	Age  uint
}

func ReflectStruct(arg interface{}) {
	t := reflect.TypeOf(arg)
	v := reflect.ValueOf(arg)
	fmt.Printf("Type: %v, Value: %v\n", t, v)

	for i := 0; i < t.NumField(); i++ {
		field := t.Field(i)
		fieldValue := v.Field(i)
		fmt.Printf("%5v: %10v=%5v\n", field.Name, field.Type, fieldValue)
	}
}

func main() {
	user := User{1, "Go", 15}
	ReflectStruct(user)
}
```

# 获取结构体 `Tag`

结构体可以为字段定义 `Tag`，然后利用反射机制获取：

```go
package main

import (
	"fmt"
	"reflect"
)

type User struct {
	ID   uint
	Name string `json:"name" sql:"nickname"`
	Age  uint
}

func main() {
	user := User{1, "Go", 15}
	t := reflect.TypeOf(user)
	field := t.Field(1)
	fmt.Println(field.Tag.Get("json"), field.Tag.Get("sql"), field.Tag.Get("fmt"))
}
```

结果：

```shell
name nickname 
```

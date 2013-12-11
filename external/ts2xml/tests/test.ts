interface Shape {
   name: string;
   width: number;
   height: number;
   color?: string;
}
 
function area(shape : Shape) {
   var area = shape.width * shape.height;
   return "I'm " + shape.name + " with area " + area + " cm squared";
}
 
console.log( area( {name: "rectangle", width: 30, height: 15} ) );
console.log( area( {name: "square", width: 30, height: 30, color: "blue"} ) );






var shape = {
   name: "rectangle",
   popup: function() {
 
      console.log('This inside popup(): ' + this.name);
 
      setTimeout( () => {
         console.log('This inside setTimeout(): ' + this.name);
         console.log("I'm a " + this.name + "!");
      }, 3000);
 
   }
};
 
shape.popup();


class Shape {
 
   area: number;
   color: string;
 
   constructor ( name: string, width: number, height: number ) {
      this.area = width * height;
      this.color = "pink";
   }
 
   shoutout() {
      return "I'm " + this.color + " " + this.name +  " with an area of " + this.area + " cm squared.";
   }
}
 
var square = new Shape("square", 30, 30);



class Vehicule{
   consumption: number;
   wheels: number;
   constructor (c:number,w:number){
      this.consumption = c;
      this.wheels = w;
   }
}

var v = new Vehicule;
var v2 : Vehicule = new Vehicule(5,5);
console.log(v.consumption);
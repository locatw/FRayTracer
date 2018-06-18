module FRayTracer

open System
open System.IO
open System.Text
open System.Threading

[<Measure>] type rad

[<Measure>] type degree

let toDegree (x : float<rad>) =
    LanguagePrimitives.FloatWithMeasure<degree>((float x) * 180.0 / Math.PI)

let toRadian (x : float<degree>) =
    LanguagePrimitives.FloatWithMeasure<rad>((float x) * Math.PI / 180.0)

type Vector =
    val X : float
    val Y : float
    val Z : float

    new(value) =
        new Vector(value, value, value)

    new(x, y, z) =
        { X = x; Y = y; Z = z }

    static member inline (~-) (v : Vector) =
        new Vector(-v.X, -v.Y, -v.Z)

    static member inline (+) (v1 : Vector, v2 : Vector) =
        new Vector(v1.X + v2.X, v1.Y + v2.Y, v1.Z + v2.Z)

    static member inline (-) (v1 : Vector, v2 : Vector) =
        new Vector(v1.X - v2.X, v1.Y - v2.Y, v1.Z - v2.Z)

    static member inline (*) (v1 : Vector, v2 : Vector) =
        v1.X * v2.X + v1.Y * v2.Y + v1.Z * v2.Z

    static member inline (*) (a : float, v : Vector) =
        new Vector(a * v.X, a * v.Y, a * v.Z)

    static member inline (*) (v : Vector, a : float) =
        a * v

    static member inline (/) (v : Vector, a : float) =
        new Vector(v.X / a, v.Y / a, v.Z / a)

let inline length v =
    sqrt (v * v)

let inline normalize (v : Vector) = 
    let len = length v
    new Vector(v.X / len, v.Y / len, v.Z / len)

let inline cross (v1 : Vector) (v2 : Vector) =
    let x = v1.Y * v2.Z - v1.Z * v2.Y
    let y = v1.Z * v2.X - v1.X * v2.Z
    let z = v1.X * v2.Y - v1.Y * v2.X
    new Vector(x, y, z)

type Fov = float<rad>

let createFovByDegree (x : float<degree>) = (toRadian x)

type Ray =
    val Origin : Vector
    val Direction : Vector

    new(origin, direction) =
        { Origin = origin; Direction = normalize direction }

type Camera =
    val Origin : Vector
    val Direction : Vector
    val Up : Vector
    val Fov : Fov

    new(origin, direction, up, fov) =
        { Origin = origin; Direction = normalize direction; Up = normalize up; Fov = fov }

type Color =
    { R : float; G : float; B : float }

    static member inline (+) (color1 : Color, color2 : Color) =
        { R = color1.R + color2.R; G = color1.G + color2.G; B = color1.B + color2.B }

    static member inline (*) (color1 : Color, color2 : Color) =
        { R = color1.R * color2.R; G = color1.G * color2.G; B = color1.B * color2.B }

    static member inline (*) (a : float, color : Color) =
        { R = a * color.R; G = a * color.G; B = a * color.B }

    static member inline (*) (color : Color, a : float) =
        a * color

    static member inline (/) (color : Color, a : float) =
        { R = color.R / a; G = color.G / a; B = color.B / a }
    
    static member Black = { R = 0.0; G = 0.0; B = 0.0 }
    
    static member White = { R = 1.0; G = 1.0; B = 1.0 }

type Material = { Diffuse : Color; Emission : Color }

type Sphere =
    val Center : Vector
    val Radius : float
    val Material : Material

    new(center, radius, material) =
        if radius <= 0.0 then raise (new ArgumentException("radius must be greater than 0", "radius"))
        { Center = center; Radius = radius; Material = material }

type Plane =
    val Center : Vector
    val Normal : Vector
    val Material : Material

    new(center, normal, material) =
        { Center = center; Normal = normalize normal; Material = material }

[<NoComparison>]
type SceneObject =
| Sphere of Sphere
| Plane of Plane

[<NoComparison>]
type Scene = { Objects : SceneObject list; Camera : Camera }

type HitInfo =
    val Object : SceneObject
    val Position : Vector
    val Normal : Vector
    val T : float

    new(object, position, normal, t) =
        if t <= 0.0 then raise (new ArgumentException("t must be greater than 0", "t"))
        { Object = object; Position = position; Normal = normalize normal; T = t }

let intersectSphere (ray : Ray) (sphere : Sphere) =
    let oc = ray.Origin - sphere.Center
    let b = 2.0 * (ray.Direction * oc)
    let c = (pown (length oc) 2) - (pown sphere.Radius 2)
    let d = b * b - 4.0 * c
    let t =
        match d with
        | d when 0.0 < d ->
            let dd = sqrt d
            let t1 = (-b + dd) / 2.0
            let t2 = (-b - dd) / 2.0

            if 0.0 < t1 && 0.0 < t2 then Some (min t1 t2)
            elif t1 < 0.0 && t2 < 0.0 then None
            else Some (max t1 t2)
        | d when d < 0.0 -> None
        | _ -> Some (-b / 2.0)

    match t with
    | Some t ->
        let position = ray.Origin + t * ray.Direction
        let normal = normalize (position - sphere.Center)
        Some (new HitInfo(Sphere sphere, position, normal, t))
    | None -> None

let intersectPlane (ray : Ray) (plane : Plane) =
    let a = ray.Direction * plane.Normal
    if a <> 0.0 then
        let b = (plane.Center - ray.Origin) * plane.Normal
        let t = b / a
        if 0.0 < t then
            let position = t * ray.Direction + ray.Origin
            Some (new HitInfo(Plane plane, position, plane.Normal, t))
        else
            None
    else
        None

let intersect (ray : Ray) object =
    match object with
    | Sphere sphere -> intersectSphere ray sphere
    | Plane plane -> intersectPlane ray plane

type Coordinate = { X : int; Y : int }

type Image = { Width : int; Height : int; Data : Color array }

let getMaterial =
    function
    | Sphere x -> x.Material
    | Plane x -> x.Material

// ref: http://neue.cc/2013/03/06_399.html
[<AbstractClass; Sealed>]
type RandomProvider private() =
    static let mutable seed = Environment.TickCount

    static member private randomWrapper =
        new ThreadLocal<Random>(fun () ->
            Interlocked.Increment(&seed) |> ignore
            new Random(seed))

    static member GetThreadRandom() : Random =
        RandomProvider.randomWrapper.Value

let distanceAttenuation (color : Color) (ray : Ray) (hitInfo : HitInfo) =
    let distance = length (hitInfo.Position - ray.Origin)
    color / (1.0 + 0.01 * (pown distance 2))

let createIndirectRay (hitInfo : HitInfo) =
    let random = RandomProvider.GetThreadRandom()
    let x = 2.0 * random.NextDouble() - 1.0
    let y = 2.0 * random.NextDouble() - 1.0
    let z = 2.0 * random.NextDouble() - 1.0
    let normal =
        let n = normalize (new Vector(x, y, z))
        if 0.0 <= hitInfo.Normal * n then n else -n
    let origin = hitInfo.Position + 0.001 * hitInfo.Normal
    new Ray(origin, normal)

let rec traceRay (scene : Scene) depth (ray : Ray) : Color =
    let hitInfo =
        scene.Objects
        |> List.map (intersect ray)
        |> List.choose id
        |> function
           | [] -> None
           | x -> Some (x |> List.minBy (fun hitInfo -> hitInfo.T))
    match hitInfo with
    | Some hitInfo ->
        let material = getMaterial hitInfo.Object
        let emissionColor = material.Emission

        if emissionColor.R <> 0.0 || emissionColor.G <> 0.0 || emissionColor.B <> 0.0 then
            let emission = material.Emission * (-ray.Direction * hitInfo.Normal)
            distanceAttenuation emission ray hitInfo
        elif 1 < depth then
            let indirectRay = createIndirectRay hitInfo
            let color = traceRay scene (depth - 1) indirectRay

            let diffuse = material.Diffuse * color * (-ray.Direction * hitInfo.Normal)
            distanceAttenuation diffuse ray hitInfo
        else
            Color.Black
    | None -> Color.Black

let createPixelRays (camera : Camera) (width : int) (height : int) samplingCount coord =
    let aspect = (float width) / (float height)

    let screenXAxis = cross camera.Direction camera.Up |> normalize
    let screenYAxis = -camera.Up
    let screenWidth = 2.0 * tan ((float camera.Fov) / 2.0)
    let screenHeight = screenWidth / aspect
    let screenCenter = camera.Origin + camera.Direction

    let pixelWidth = screenWidth / (float width)
    let pixelHeight = screenHeight / (float height)
    let offset = (pixelWidth / 2.0) * screenXAxis + (pixelHeight / 2.0) * screenYAxis
    let leftTopPixelCenter =
        screenCenter
        - (screenWidth / 2.0) * screenXAxis
        - (screenHeight / 2.0) * screenYAxis
        + offset
    let pixelCenter =
        leftTopPixelCenter 
        + (float coord.X) * pixelWidth * screenXAxis
        + (float coord.Y) * pixelHeight * screenYAxis

    seq {
        let random = RandomProvider.GetThreadRandom()
        for _ in 0..(samplingCount- 1) do
            let x = random.NextDouble() - 0.5
            let y = random.NextDouble() - 0.5
            yield (x, y)
    }
    |> Seq.map (fun (x, y) -> pixelCenter + x * pixelWidth * screenXAxis + y * pixelHeight * screenYAxis)
    |> Seq.map (fun subPixelPos -> new Ray(camera.Origin, subPixelPos - camera.Origin))
    |> Seq.toArray

let renderPixel scene width height coord =
    let samplingCount = 1000
    let color =
        createPixelRays scene.Camera width height samplingCount coord
        |> Array.Parallel.map (traceRay scene 10)
        |> Array.reduce (fun acc color -> acc + color)
    color / (float samplingCount)

let render scene (width : int) (height : int) =
    let coords =
        seq {
            for y in 0..(height - 1) do
                for x in 0..(width - 1) do
                    yield { X = x; Y = y } 
        }
        |> Seq.toArray
    let len = Array.length coords
    let data =
        coords
        |> Array.mapi (
            fun i coord ->
                let pixelColor = renderPixel scene width height coord
                if i % 500 = 0 then
                    let progress = ((float i ) / (float len)) * 100.0
                    printfn "Progress: %.1f %%" progress
                pixelColor)
    { Width = width; Height = height; Data = data }
    
let clamp minValue maxValue x = 
    x |> max minValue |> min maxValue

let writePpm path image =
    let pixelToArray pixel =
        [| pixel.R; pixel.G; pixel.B |]

    use file = new StreamWriter(path, false, Encoding.ASCII)
    file.WriteLine("P3")
    file.WriteLine(sprintf "%d %d" image.Width image.Height)
    file.WriteLine(255)
    for y in 0..(image.Height - 1) do
        let values =
            Array.sub image.Data (y * image.Width) image.Width
            |> Array.map pixelToArray
            |> Array.concat
            |> Array.map (fun x -> 255.0 * x)
            |> Array.map round
            |> Array.map (clamp 0.0 255.0)
            |> Array.map int
            |> Array.map string
        let line = String.Join(" ", values)
        file.WriteLine(line)

let createScene () =
    let camera = new Camera(new Vector(0.0, 0.0, 20.0), new Vector(0.0, 0.0, -1.0), new Vector(0.0, 1.0, 0.0), createFovByDegree 60.0<degree>) 
    let spheres =
        [
            new Sphere(new Vector(3.0, -3.0, 2.0), 2.0, { Diffuse = Color.White; Emission = Color.Black })
            new Sphere(new Vector(-3.0, -3.0, -1.0), 2.0, { Diffuse = Color.White; Emission = Color.Black })
        ] |> List.map Sphere
    let planes =
        [
            new Plane(new Vector(0.0, 5.0, 0.0), new Vector(0.0, -1.0, 0.0), { Diffuse = Color.Black; Emission = 30.0 * Color.White }) // top
            new Plane(new Vector(0.0, -5.0, 0.0), new Vector(0.0, 1.0, 0.0), { Diffuse = Color.White; Emission = Color.Black }) // bottom
            new Plane(new Vector(-6.0, 0.0, 0.0), new Vector(1.0, 0.0, 0.0), { Diffuse = { R = 1.0; G = 0.0; B = 0.0 }; Emission = Color.Black }) // left
            new Plane(new Vector(6.0, 0.0, 0.0), new Vector(-1.0, 0.0, 0.0), { Diffuse = { R = 0.0; G = 0.0; B = 1.0 }; Emission = Color.Black }) // right
            new Plane(new Vector(0.0, 0.0, -5.0), new Vector(0.0, 0.0, 1.0), { Diffuse = Color.White; Emission = Color.Black }) // back
            new Plane(new Vector(0.0, 0.0, 25.0), new Vector(0.0, 0.0, -1.0), { Diffuse = Color.White; Emission = Color.Black }) // front
        ] |> List.map Plane
        
    { Objects = spheres @ planes; Camera = camera }

[<EntryPoint>]
let main _ =
    let width = 160
    let height = 120
    //let width = 640
    //let height = 480
    let scene = createScene ()

    let stopWatch = Diagnostics.Stopwatch.StartNew()
    let image = render scene width height
    stopWatch.Stop()

    let seconds = stopWatch.Elapsed.TotalSeconds
    printfn "%.3f [s]" seconds

    writePpm "output.ppm" image
    0
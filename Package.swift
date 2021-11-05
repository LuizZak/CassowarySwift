// swift-tools-version:4.2
import PackageDescription

let package = Package(
    name: "CassowarySwift",
    products: [
        .library(
            name: "CassowarySwift",
            targets: ["CassowarySwift"]),
    ],
    targets: [
        .target(
            name: "CassowarySwift",
            dependencies: []),
        .testTarget(
            name: "CassowarySwiftTests",
            dependencies: ["CassowarySwift"]),
    ]
)

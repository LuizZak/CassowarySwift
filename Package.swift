// swift-tools-version:5.0
import PackageDescription

let package = Package(
    name: "CassowarySwift",
    products: [
        .library(
            name: "CassowarySwift",
            targets: ["CassowarySwift"]
        ),
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-collections.git", from: "1.3.0"),
    ],
    targets: [
        .target(
            name: "CassowarySwift",
            dependencies: [
                .product(name: "OrderedCollections", package: "swift-collections"),
            ]
        ),
        .testTarget(
            name: "CassowarySwiftTests",
            dependencies: ["CassowarySwift"]
        ),
    ]
)

use burn::tensor::{Device, DeviceKind, Distribution, Tensor};
use std::time::Instant;

fn main() {
    let device = Device::vulkan(DeviceKind::DiscreteGpu(0)).autodiff();
    println!("device: {device:?}");
    let a: Tensor<2> = Tensor::random([1024, 1024], Distribution::Default, &device).require_grad();
    let b: Tensor<2> = Tensor::random([1024, 1024], Distribution::Default, &device);
    let n: usize = std::env::args().nth(1).map_or(5, |v| v.parse().unwrap());
    for i in 0..n {
        let t = Instant::now();
        let loss = a.clone().matmul(b.clone()).powf_scalar(2.0).mean();
        let grads = loss.backward();
        let g: f32 = a.grad(&grads).unwrap().slice([0..1, 0..1]).into_scalar();
        println!("step {i}: loss {} grad {g} in {:?}", loss.into_scalar::<f32>(), t.elapsed());
    }
}

# ercp_basic.rs

`ercp_basic` is an implementation of [ERCP
Basic](https://github.com/ercp/specifications/blob/v0.1.0/spec/ercp_basic.md) in
Rust. It has support for both `no_std` and `std` environments, and provide
several adapters for the underlying protocol.

# Example

```rust
#![no_std]
#![no_main]

use panic_halt as _;

use rtic::app;

use stm32l4xx_hal::{
    gpio::{Alternate, Floating, Input, AF7, PA10, PA9},
    pac::USART1,
    prelude::*,
    serial::{self, Config, Serial},
};

use ercp_basic::{adapter::SerialAdapter, DefaultRouter, ErcpBasic};

/// The UART we use for ERCP.
type Uart = Serial<
    USART1,
    (
        PA9<Alternate<AF7, Input<Floating>>>,
        PA10<Alternate<AF7, Input<Floating>>>,
    ),
>;

// Rx buffer size.
const RX_MAX_LEN: usize = 255;

#[app(device = stm32l4xx_hal::pac, peripherals = true)]
const APP: () = {
    struct Resources {
        ercp: ErcpBasic<SerialAdapter<Uart>, DefaultRouter, RX_MAX_LEN>,
    }

    #[init]
    fn init(cx: init::Context) -> init::LateResources {
        let dp = cx.device;

        // Clock configuration.
        let mut rcc = dp.RCC.constrain();
        let mut flash = dp.FLASH.constrain();
        let mut pwr = dp.PWR.constrain(&mut rcc.apb1r1);
        let clocks = rcc.cfgr.freeze(&mut flash.acr, &mut pwr);

        // Serial port configuration.
        let mut gpioa = dp.GPIOA.split(&mut rcc.ahb2);
        let tx_pin = gpioa.pa9.into_af7(&mut gpioa.moder, &mut gpioa.afrh);
        let rx_pin = gpioa.pa10.into_af7(&mut gpioa.moder, &mut gpioa.afrh);
        let mut serial = Serial::usart1(
            dp.USART1,
            (tx_pin, rx_pin),
            Config::default().baudrate(115_200.bps()),
            clocks,
            &mut rcc.apb2,
        );

        // Listen RX events.
        serial.listen(serial::Event::Rxne);

        // ERCP configuration.
        let adapter = SerialAdapter::new(serial);
        let mut ercp = ErcpBasic::new(adapter, DefaultRouter);

        ercp.log("Firmware initialised!").ok();

        init::LateResources { ercp }
    }

    #[task(binds = USART1, resources = [ercp], spawn = [ercp_process])]
    fn usart1(cx: usart1::Context) {
        let ercp = cx.resources.ercp;

        ercp.handle_data();

        if ercp.complete_frame_received() {
            cx.spawn.ercp_process().ok();
        }
    }

    #[task(resources = [ercp])]
    fn ercp_process(cx: ercp_process::Context) {
        cx.resources.ercp.process(&mut ());
    }

    extern "C" {
        fn TIM2();
    }
};
```

# [Contributing](CONTRIBUTING.md)

Before contributing to this project, please read the
[CONTRIBUTING.md](CONTRIBUTING.md).

# License

Copyright © 2021 Jean-Philippe Cugnet

This project is licensed under the [MIT license](LICENSE).

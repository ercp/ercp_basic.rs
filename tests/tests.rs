// Copyright 2021-2022 Jean-Philippe Cugnet
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::{
    cell::RefCell,
    collections::VecDeque,
    sync::{Arc, Mutex},
    thread,
};

use ercp_basic::{Adapter, DefaultRouter, ErcpBasic, Router};

struct DummyAdapter;

struct MemoryAdapter {
    read: Arc<Mutex<RefCell<VecDeque<u8>>>>,
    write: Arc<Mutex<RefCell<VecDeque<u8>>>>,
}

struct CustomRouter;

impl MemoryAdapter {
    fn new() -> (Self, Self) {
        let host = Self {
            read: Arc::new(Mutex::new(RefCell::new(VecDeque::new()))),
            write: Arc::new(Mutex::new(RefCell::new(VecDeque::new()))),
        };

        let device = Self {
            read: host.write.clone(),
            write: host.read.clone(),
        };

        (host, device)
    }
}

impl Adapter for DummyAdapter {
    type Error = ();

    fn read(&mut self) -> Result<Option<u8>, ()> {
        Ok(None)
    }

    fn write(&mut self, _byte: u8) -> Result<(), ()> {
        Ok(())
    }
}

impl Adapter for MemoryAdapter {
    type Error = ();

    fn read(&mut self) -> Result<Option<u8>, ()> {
        Ok(self.read.lock().unwrap().get_mut().pop_back())
    }

    fn write(&mut self, byte: u8) -> Result<(), ()> {
        self.write.lock().unwrap().get_mut().push_front(byte);
        Ok(())
    }
}

impl Router<255> for CustomRouter {
    type Context = ();

    fn route(
        &mut self,
        command: ercp_basic::Command,
        _ctx: &mut Self::Context,
    ) -> Option<ercp_basic::Command> {
        self.default_routes(command)
    }

    fn firmware_version(&self) -> &str {
        "Test version"
    }

    fn description(&self) -> &str {
        "Test ERCP device"
    }
}

#[test]
fn an_ercp_basic_driver_can_be_instantiated() {
    ErcpBasic::<_, _>::new(DummyAdapter, DefaultRouter);
}

#[test]
fn commands_are_processed_when_calling_accept_command() {
    let (host_adapter, device_adapter) = MemoryAdapter::new();
    let mut host = ErcpBasic::<_, _>::new(host_adapter, DefaultRouter);
    let mut device = ErcpBasic::<_, _>::new(device_adapter, DefaultRouter);

    thread::spawn(move || device.accept_command(&mut ()));
    assert_eq!(host.ping(), Ok(Ok(())));
}

#[test]
fn it_is_possisble_to_define_a_custom_router() {
    let (host_adapter, device_adapter) = MemoryAdapter::new();
    let mut host = ErcpBasic::<_, _>::new(host_adapter, DefaultRouter);
    let mut device = ErcpBasic::<_, _>::new(device_adapter, CustomRouter);

    thread::spawn(move || device.accept_command(&mut ()));

    let mut description = [0; 100];
    assert_eq!(
        host.description(&mut description),
        Ok(Ok(CustomRouter.description().len()))
    );
    assert_eq!(
        &description[0..CustomRouter.description().len()],
        CustomRouter.description().as_bytes()
    );
}

// TODO: Custom command creation.

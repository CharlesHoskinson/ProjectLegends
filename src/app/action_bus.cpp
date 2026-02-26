// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ActionBus — dispatch implementation.

#include "app/action_bus.h"

namespace legends {

void ActionBus::dispatch(Action action, int param) {
    ++dispatch_count_;
    auto it = handlers_.find(action);
    if (it != handlers_.end()) {
        for (auto& handler : it->second) {
            handler(param);
        }
    }
}

void ActionBus::registerHandler(Action action, Handler handler) {
    handlers_[action].push_back(std::move(handler));
}

void ActionBus::clearHandlers(Action action) {
    handlers_.erase(action);
}

void ActionBus::clearAll() {
    handlers_.clear();
}

size_t ActionBus::handlerCount(Action action) const {
    auto it = handlers_.find(action);
    if (it != handlers_.end()) {
        return it->second.size();
    }
    return 0;
}

} // namespace legends
